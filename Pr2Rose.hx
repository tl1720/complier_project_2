// [NYU Courant Institute] Compiler Construction/Fall 2015 -*-hacs-*-
//
// Grammar and some utilities  for Milestone 2 (remember to rename).
//
// Based on "Pr1Rose.hx"[1] extended with rules from "Pr2Rose-SDD"[2] solution
// and some helpers developed during lecture 8.
//
// [1]\url{http://cs.nyu.edu/courses/fall15/CSCI-GA.2130-001/project1/Pr1Rose.hx}
// [2]\url{http://cs.nyu.edu/courses/fall15/CSCI-GA.2130-001/project2/SubScript-SDD.pdf}
//
// This file is Copyright © 2015 Kristoffer Rose ⟨krisrose@crsx.org⟩
// and licensed under the CC-BY-4.0 license.

module edu.nyu.csci.cc.fall15.Pr2Rose {

  ////////////////////////////////////////////////////////////////////////
  // GRAMMAR FROM MILESTONE 1.
  //
  // [1] references are to the Project Milestone 1 assignment.
  
  //  [1]1.1. LEXICAL CONVENTIONS

  // Ignore:
  space [ \t\n\r] | "//" .*			// white space
    | "/*" ( [^*] | "*" [^/] )* "*/"  ;		// non-nested C comments

  // We have identifiers, integers, and strings.
  token IDENTIFIER  | ⟨LetterEtc⟩ (⟨LetterEtc⟩ | ⟨Digit⟩)* ;
  token INTEGER	    | ⟨Digit⟩+ ;
  token STRING	    | "\'" ( [^\'\\\n] | \\ ⟨Escape⟩ )* "\'"
    | "\"" ( [^\"\\\n] | \\ ⟨Escape⟩ )* "\""
    ;

  // Lexical helpers.
  token fragment Letter	    | [A-Za-z] ;
  token fragment LetterEtc  | ⟨Letter⟩ | [$_] ;
  token fragment Digit	    | [0-9] ;
  token fragment Escape	 | [\n\\nt''""] | "x" ⟨Hex⟩ ⟨Hex⟩ ;
  token fragment Hex	 | [0-9A-Fa-f] ;

  // [1]1.2. EXPRESSIONS
  //
  // Each operator is assigned a \HAX precedence following Figure 1.

  sort Expression

    |  ⟦ ⟨IDENTIFIER⟩ ⟧@13
    |  ⟦ ⟨STRING⟩ ⟧@13
    |  ⟦ ⟨INTEGER⟩ ⟧@13
    |  sugar ⟦ ( ⟨Expression#e⟩ ) ⟧@13 → #e

    |  ⟦ ⟨Expression@12⟩ . ⟨IDENTIFIER⟩ ⟧@12
    |  ⟦ ⟨Expression@12⟩ ( ⟨ExpressionList⟩ ) ⟧@12

    |  ⟦ ! ⟨Expression@11⟩ ⟧@11
    |  ⟦ ~ ⟨Expression@11⟩ ⟧@11
    |  ⟦ - ⟨Expression@11⟩ ⟧@11
    |  ⟦ + ⟨Expression@11⟩ ⟧@11

    |  ⟦ ⟨Expression@10⟩ * ⟨Expression@11⟩ ⟧@10
    |  ⟦ ⟨Expression@10⟩ / ⟨Expression@11⟩ ⟧@10
    |  ⟦ ⟨Expression@10⟩ % ⟨Expression@11⟩ ⟧@10

    |  ⟦ ⟨Expression@9⟩ + ⟨Expression@10⟩ ⟧@9
    |  ⟦ ⟨Expression@9⟩ - ⟨Expression@10⟩ ⟧@9

    |  ⟦ ⟨Expression@9⟩ < ⟨Expression@9⟩ ⟧@8
    |  ⟦ ⟨Expression@9⟩ > ⟨Expression@9⟩ ⟧@8
    |  ⟦ ⟨Expression@9⟩ <= ⟨Expression@9⟩ ⟧@8
    |  ⟦ ⟨Expression@9⟩ >= ⟨Expression@9⟩ ⟧@8

    |  ⟦ ⟨Expression@8⟩ == ⟨Expression@8⟩ ⟧@7
    |  ⟦ ⟨Expression@8⟩ != ⟨Expression@8⟩ ⟧@7

    |  ⟦ ⟨Expression@6⟩ & ⟨Expression@7⟩ ⟧@6
    |  ⟦ ⟨Expression@5⟩ ^ ⟨Expression@6⟩ ⟧@5
    |  ⟦ ⟨Expression@4⟩ | ⟨Expression@5⟩ ⟧@4

    |  ⟦ ⟨Expression@3⟩ && ⟨Expression@4⟩ ⟧@3
    |  ⟦ ⟨Expression@2⟩ || ⟨Expression@3⟩ ⟧@2

    |  ⟦ ⟨Expression@2⟩ ? ⟨Expression⟩ : ⟨Expression@1⟩ ⟧@1

    |  ⟦ ⟨Expression@1⟩ = ⟨Expression⟩ ⟧
    |  ⟦ ⟨Expression@1⟩ += ⟨Expression⟩ ⟧
    |  ⟦ ⟨Expression@1⟩ = { ⟨KeyValueList⟩ } ⟧
    ;

  // Helper to describe actual list of arguments of function call.
  sort ExpressionList | ⟦ ⟨Expression⟩ ⟨ExpressionListTail⟩ ⟧  |  ⟦⟧ ;
  sort ExpressionListTail | ⟦ , ⟨Expression⟩ ⟨ExpressionListTail⟩ ⟧  |	⟦⟧ ;

  // Helper to describe list of key-value pairs.
  sort KeyValueList  |	⟦ ⟨KeyValue⟩ ⟨KeyValueListTail⟩ ⟧  |  ⟦⟧ ;
  sort KeyValueListTail	  |  ⟦ , ⟨KeyValue⟩ ⟨KeyValueListTail⟩ ⟧  |  ⟦⟧ ;
  sort KeyValue	      |	 ⟦ ⟨IDENTIFIER⟩ : ⟨Expression⟩ ⟧ ;

  // [1]1.3. TYPES
  //
  // Covers the cases of Figure 2.

  sort Type
    |  ⟦ boolean ⟧
    |  ⟦ number ⟧
    |  ⟦ string ⟧
    |  ⟦ void ⟧
    |  ⟦ ⟨IDENTIFIER⟩ ⟧
    |  ⟦ ( ⟨TypeList⟩ ) => ⟨Type⟩ ⟧
    |  ⟦ { ⟨NameTypeList⟩ } ⟧
    ;

  // Helper to describe list of types of arguments of function call.
  sort TypeList | ⟦ ⟨Type⟩ ⟨TypeListTail⟩ ⟧ |  ⟦⟧ ;
  sort TypeListTail | ⟦ , ⟨Type⟩ ⟨TypeListTail⟩ ⟧ | ⟦⟧ ;

  // Helper to describe list of names with types.
  sort NameTypeList  |	⟦ ⟨NameType⟩ ⟨NameTypeListTail⟩ ⟧  |  ⟦⟧ ;
  sort NameTypeListTail	  |  ⟦ , ⟨NameType⟩ ⟨NameTypeListTail⟩ ⟧  |  ⟦⟧ ;
  sort NameType	      |	 ⟦ ⟨IDENTIFIER⟩ : ⟨Type⟩ ⟧ ;

  // [1]1.4. STATEMENTS
  //
  // Cases from Figure 3. Dangling else handled with LL order trick from class slides.

  sort Statement
    |  ⟦ { ⟨Statements⟩ } ⟧
    |  ⟦ var ⟨NameType⟩ ; ⟧
    |  ⟦ ⟨Expression⟩ ; ⟧
    |  ⟦ ; ⟧
    |  ⟦ if ( ⟨Expression⟩ ) ⟨IfTail⟩ ⟧
    |  ⟦ while ( ⟨Expression⟩ ) ⟨Statement⟩ ⟧
    |  ⟦ return ⟨Expression⟩ ; ⟧
    |  ⟦ return ; ⟧
    ;
  sort Statements | ⟦ ⟨Statement⟩ ⟨Statements⟩ ⟧   |  ⟦⟧ ;

  sort IfTail | ⟦ ⟨Statement⟩ else ⟨Statement⟩ ⟧  | ⟦ ⟨Statement⟩ ⟧ ;  // eagerly consume elses

  // [1]1.5. DECLARATIONS
  //
  // Straight encoding.
  
  sort Declaration
    |  ⟦ interface ⟨IDENTIFIER⟩ { ⟨Members⟩ } ⟧
    |  ⟦ function ⟨IDENTIFIER⟩ ⟨CallSignature⟩ { ⟨Statements⟩ } ⟧
    ;

  sort Member
    |  ⟦ ⟨IDENTIFIER⟩ : ⟨Type⟩ ; ⟧
    |  ⟦ ⟨IDENTIFIER⟩ ⟨CallSignature⟩ { ⟨Statements⟩ } ⟧
    ;
  sort Members	|  ⟦ ⟨Member⟩ ⟨Members⟩ ⟧    |	⟦⟧ ;

  sort CallSignature  |	 ⟦ ( ⟨NameTypeList⟩ ) : ⟨Type⟩ ⟧ ;

  // [1]1.6. PROGRAM
  //
  // Straight encoding, using Unit for the combination of statements and declarations,
  // with at least one Unit. Program is main input sort.

  main sort Program  |	⟦ ⟨Units⟩ ⟧ ;

  sort Units  |	 ⟦ ⟨Unit⟩ ⟨Units⟩ ⟧  |	⟦ ⟨Unit⟩ ⟧ ;
  sort Unit  |	⟦ ⟨Declaration⟩ ⟧  |  ⟦ ⟨Statement⟩ ⟧ ;

  ////////////////////////////////////////////////////////////////////////
  // IMPLEMENTATION OF SYNTAX-DIRECTED DEFINITION
  //
  // [2] references are to the Pr2Rose-SDD.pdf solution.
  
  // [2]1.3. BOOLEANS

  sort Bool | True | False;
  | scheme And(Bool, Bool);  And(False, #2) → False;  And(True, #2) → #2;
  | scheme Or(Bool,Bool);  Or(False, #2) → #2;  Or(True, #2) → True;
  | scheme Not(Bool);  Not(False) → True;  Not(True) → False;

  // [2]1.4. TUPLES
  // We avoid pairs and use syntax constructions instead:

  // - ⟨Symbol,Type⟩ pairs are represented using NameType.

  // [2]1.5. VECTORS
  // We avoid vectors and use syntax constructions instead:

  // - Vectors of IDENTIFIER are just Names.
  sort Names | NamesNil | NamesCons(IDENTIFIER, Names);

  //  - membership (∈).
  sort Bool | scheme InNames(IDENTIFIER, Names);
  InNames(#ID, NamesNil) → False;
  InNames(#ID, NamesCons(#ID, #rest)) → True;
  default InNames(#ID, NamesCons(#ID2, #rest)) → InNames(#ID, #rest);

  //  - removal (\).
  sort Names | scheme NamesBut(Names, IDENTIFIER);
  NamesBut(NamesNil, #ID) → NamesNil;
  NamesBut(NamesCons(#ID, #rest), #ID) → #rest;
  default NamesBut(NamesCons(#ID2, #rest), #ID) → NamesBut(#rest, #ID);
  
  // - Vectors of Type are represented using TypeListTail.
  //  - So ε and ∥ are implemented as follows:
  sort TypeListTail;
  | scheme AppendTypes(TypeListTail, TypeListTail);
  AppendTypes(⟦⟧, #2) → #2;
  AppendTypes(⟦ , ⟨Type#11⟩ ⟨TypeListTail#12⟩ ⟧, #2)
    → ⟦ , ⟨Type#11⟩ ⟨TypeListTail AppendTypes(#12, #2) ⟩ ⟧;

  //  - special helpers convert to and from TypeList
  sort TypeList | scheme UnTailTypes(TypeListTail);
  UnTailTypes(⟦⟧) → ⟦⟧;
  UnTailTypes(⟦ , ⟨Type#1⟩ ⟨TypeListTail#2⟩ ⟧) → ⟦ ⟨Type#1⟩ ⟨TypeListTail#2⟩ ⟧;
  sort TypeListTail | scheme TailTypes(TypeList);
  TailTypes(⟦⟧) → ⟦⟧;
  TailTypes(⟦ ⟨Type#1⟩ ⟨TypeListTail#2⟩ ⟧) → ⟦ , ⟨Type#1⟩ ⟨TypeListTail#2⟩ ⟧;
  
  // - Vectors of ⟨Symbol,Type⟩ are represented using NameTypeListTail.
  //   So ε is just ⟦⟧ and ∥ is implemented as follows:
  sort NameTypeListTail;
  | scheme AppendNameTypes(NameTypeListTail, NameTypeListTail);
  AppendNameTypes(⟦⟧, #2) → #2;
  AppendNameTypes(⟦ , ⟨NameType#11⟩ ⟨NameTypeListTail#12⟩ ⟧, #2)
    → ⟦ , ⟨NameType#11⟩ ⟨NameTypeListTail AppendNameTypes(#12, #2) ⟩ ⟧ ;
  | scheme TailNameTypes(NameTypeList);
  TailNameTypes(⟦ ⟨NameType#1⟩ ⟨NameTypeListTail#2⟩ ⟧)
    → ⟦ , ⟨NameType#1⟩ ⟨NameTypeListTail#2⟩ ⟧;
  
  // - We make sure to create ⟨Symbol, Type⟩ pairs with fully evaluated IDENTIFIERs.
  sort NameTypeListTail | scheme SingletonNameTypes(IDENTIFIER, Type);
  SingletonNameTypes(#id, #type) → ⟦ , ⟨IDENTIFIER#id⟩ : ⟨Type#type⟩ ⟧;
  
  // - The special notation  { name-type-pairs }  for a Type then becomes:
  sort Type | scheme MakeInterfaceType(NameTypeListTail);
  MakeInterfaceType(⟦⟧) → ⟦ { } ⟧;
  MakeInterfaceType(⟦ , ⟨NameType#1⟩ ⟨NameTypeListTail#2⟩ ⟧)
    → ⟦ { ⟨NameType#1⟩ ⟨NameTypeListTail#2⟩ } ⟧;

  // - Similar helper for KeyValueList
  sort KeyValueListTail | scheme TailKeyValues(KeyValueList);
  TailKeyValues(⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧)
    → ⟦ , ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧;
  
  // [2]1.6. MAPS
  // We use HACS built-in environment attributes for maps, with the usual conventions.

  // [2]1.7. NAMESPACES
  // Names are represented by IDENTIFIER tokens.
  
  // [2]1.8. ATTRIBUTES
  attribute ↑ds(NameTypeListTail);
  attribute ↑uds(NameTypeListTail);
  attribute ↓te{IDENTIFIER : Type};
  attribute ↑ts(TypeListTail);
  attribute ↑t(Type);
  attribute ↓rt(Type);
  attribute ↓mt(Type);
  attribute ↑id(IDENTIFIER);
  attribute ↓ids(Names);
  attribute ↑ok(Bool);

  // [2]1.9. SYNTAX-DIRECTED DEFINITION
  //
  // We follow the structure of the SDD strictly.
  
  // ----------
  // Rules for P.
  sort Program | ↑ok;

  // P → Us1
  //
  // Main pivot: depends on first pass and initiates second pass.

  // | Us1.te = Extend(GlobalDefs, Us1.ds)
  | scheme P2(Program);
  P2(⟦ ⟨Units#1 ↑ds(#1ds)⟩ ⟧ ↑#syn) → ⟦ ⟨Units UsteExtend(#1, AppendNameTypes(GlobalDefs, #1ds))⟩ ⟧ ↑#syn;
  
  // | P.ok = DistinctFirst(Us1.ds) ∧ Us1.ok
  ⟦ ⟨Units#1↑ds(#1ds)↑ok(#1ok)⟩ ⟧ ↑ok(And(DistinctFirst(#1ds), #1ok));
  
  // ----------
  // Rules for Us.
  sort Units | ↑ds | scheme Uste(Units)↓te | ↑ok ;
  
  | scheme UsteExtend(Units, NameTypeListTail) ↓te; // helper implementing Extend instance
  UsteExtend(#Us, ⟦⟧) → Uste(#Us);
  UsteExtend(#Us, ⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ ⟧)
    → UsteExtend(#Us, #3) ↓te{#1 : #2};

  // Us → U1 Us2
  
  // | Us.ds = U1.ds ∥ Us2.ds
  ⟦ ⟨Unit#1↑ds(#1ds)⟩ ⟨Units#2↑ds(#2ds)⟩ ⟧ ↑ds(AppendNameTypes(#1ds, #2ds));

  // | U1.te = Us.te;  Us2.te = Extend(Us.te, U1.uds)
  Uste(⟦ ⟨Unit#1↑uds(#1uds)⟩ ⟨Units#2⟩ ⟧↑#syn) → ⟦ ⟨Unit Ute(#1)⟩ ⟨Units UsteExtend(#2, #1uds)⟩ ⟧↑#syn;

  // | Us.ok = U1.ok ∧ Us2.ok
  ⟦ ⟨Unit#1↑ok(#1ok)⟩ ⟨Units#2↑ok(#2ok)⟩ ⟧ ↑ok(And(#1ok, #2ok));

  // Us → U1
  
  // | Us.ds = U1.ds
  ⟦ ⟨Unit#1↑ds(#1ds)⟩ ⟧ ↑ds(#1ds);

  // | U1.te = Us.te;
  Uste(⟦ ⟨Unit#1⟩ ⟧↑#syn) → ⟦ ⟨Unit Ute(#1)⟩ ⟧↑#syn;

  // | Us.ok = U1.ok
  ⟦ ⟨Unit#1↑ok(#1ok)⟩ ⟧ ↑ok(#1ok);

  // ----------
  // Rules for U.
  sort Unit | ↑ds | ↑uds | scheme Ute(Unit)↓te | ↑ok;

  // U → D1

  // | U.ds = D1.ds
  ⟦ ⟨Declaration#1↑ds(#1ds)⟩ ⟧ ↑ds(#1ds);

  // | U.uds = ε
  ⟦ ⟨Declaration#1⟩ ⟧ ↑uds(⟦⟧);

  // | D1.te = U.te
  Ute(⟦ ⟨Declaration#1⟩ ⟧↑#syn) → ⟦ ⟨Declaration Dte(#1)⟩ ⟧↑#syn;

  // | U.ok = D1.ok
  ⟦ ⟨Declaration#1↑ok(#1ok)⟩ ⟧ ↑ok(#1ok);

  // U → S1

  // | U.ds = ε
  ⟦ ⟨Statement#1⟩ ⟧ ↑ds(⟦⟧);

  // | U.uds = S1.uds
  ⟦ ⟨Statement#1↑ds(#1ds)⟩ ⟧ ↑uds(#1ds);

  // | S1.te = U.te
  Ute(⟦ ⟨Statement#1⟩ ⟧↑#syn) → ⟦ ⟨Statement Stert(#1) ↓rt(⟦void⟧)⟩ ⟧↑#syn;

  // | U.ok = S1.ok
  ⟦ ⟨Statement#1↑ok(#1ok)⟩ ⟧ ↑ok(#1ok);

  // ----------
  // Rules for D.
  sort Declaration | ↑ds | scheme Dte(Declaration)↓te | ↑ok;

  // D → interface id1 { Ms2 }

  // | D.ds = (⟨!+id1.sym, { Ms2.ds }⟩)
  ⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2↑ds(#2ds)⟩ } ⟧
    ↑ds(SingletonNameTypes(#1, MakeInterfaceType(#2ds)));

  // | Ms2.te = D.te
  Dte(⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2⟩ } ⟧↑#syn)
    → ⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members Mste(#2)⟩ } ⟧↑#syn;

  // | D.ok = DistinctFirst(Ms2.ds) ∧ Ms2.ok
  ⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2↑ds(#2ds)↑ok(#2ok)⟩ } ⟧
    ↑ok(And(DistinctFirst(#2ds), #2ok));

  // D → function id1 CS2 { Ss3 }

  // | D.ds = (⟨id1.sym, CS2.t⟩)
  ⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2↑t(#2t)⟩ { ⟨Statements#3⟩ } ⟧
    ↑ds(SingletonNameTypes(#1, #2t));

  // | Ss3.te = Extend(D.te, CS2.ds)
  // | Ss3.rt = CS2.rt
  Dte(⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2↑ds(#2ds)↑t(#2t)⟩ { ⟨Statements#3⟩ } ⟧↑#syn)
    → ⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2⟩ { ⟨Statements SstertExtend(#3, #2ds)↓rt(#2t)⟩ } ⟧↑#syn;
  // Notice how this rule captures both CS2.ds and CS2.t, in addition to D.te.
  // The contraction then invokes Ssrt to pass Ss3.rt, and on that result invokes SstertExtend to pass SS2.te and Ss2.rt.
  
  // | D.ok = DistinctFirst(CS2.ds) ∧ Ss3.ok
  ⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2↑ds(#2ds)⟩ { ⟨Statements#3↑ok(#3ok)⟩ } ⟧
    ↑ok(And(DistinctFirst(#2ds), #3ok));

  // ----------
  // Rules for Ms.
  sort Members | ↑ds | scheme Mste(Members)↓te | ↑ok ;

  // Ms → M1 Ms2

  // | Ms.ds = M1.ds ∥ Ms2.ds
  ⟦ ⟨Member#1↑ds(#1ds)⟩ ⟨Members#2↑ds(#2ds)⟩ ⟧ ↑ds(AppendNameTypes(#1ds, #2ds));

  // | M1.te = Ms2.te = Ms.te
  Mste(⟦ ⟨Member#1⟩ ⟨Members#2⟩ ⟧↑#syn)
    → ⟦ ⟨Member Mte(#1)⟩ ⟨Members Mste(#2)⟩ ⟧↑#syn;

  // Ms.ok = Ms1.ok ∧ Ms2.ok
  ⟦ ⟨Member#1↑ok(#1ok)⟩ ⟨Members#2↑ok(#2ok)⟩ ⟧ ↑ok(And(#1ok, #2ok));
  
  // Ms → ε
  Mste(⟦ ⟧↑#syn) → ⟦ ⟧↑#syn; //dummy

  // | Ms.ds = ε
  ⟦ ⟧ ↑ds(⟦⟧);

  // | Ms.ok = True
  ⟦ ⟧ ↑ok(True);

  // ----------
  // Rules for M.
  sort Member | ↑ds | scheme Mte(Member)↓te | ↑ok ;
  
  // M → id1 : T2 ;
  Mte(⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧ ↑#syn) → ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧ ↑#syn; //dummy

  // | M.ds = (⟨id1.sym, T2⟩)
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧ ↑ds(⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟧);

  // M.ok = True
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧ ↑ok(True);

  // M → id1 CS2 { Ss3 }

  // | M.ds = (⟨id1.sym, CS2.t⟩)
  ⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2↑t(#2t)⟩ { ⟨Statements#3⟩ } ⟧ ↑ds(⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2t⟩ ⟧);

  // | Ss3.te = Extend(M.te, CS2.ds)
  // | Ss3.rt = CS2.rt
  Mte(⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2↑ds(#2ds)↑t(#2t)⟩ { ⟨Statements#3⟩ } ⟧↑#syn)
    → ⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2⟩ { ⟨Statements SstertExtend(#3, #2ds)↓rt(#2t)⟩ } ⟧↑#syn;
  // similar to the function case

  // M.ok = DistinctFirst(CS2.ds) ∧ Ss3.ok
  ⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2↑ds(#2ds)⟩ { ⟨Statements#3↑ok(#3ok)⟩ } ⟧
    ↑ok(And(DistinctFirst(#2ds), #3ok));
  
  // ----------
  // Rules for CS.
  sort CallSignature | ↑t | ↑ds;

  // CS → ( NTL1 ) : T2

  // | CS.t = ( NTL1.ts ) => T2
  ⟦ ( ⟨NameTypeList#1↑ts(#1ts)⟩ ) : ⟨Type#2⟩ ⟧ ↑t(⟦ ( ⟨TypeList UnTailTypes(#1ts)⟩ ) => ⟨Type#2⟩ ⟧);

  // | CS.ds = NTL1.ds
  ⟦ ( ⟨NameTypeList#1↑ds(#1ds)⟩ ) : ⟨Type#2⟩ ⟧ ↑ds(#1ds);
  
  // ----------
  // Rules for NTL.
  sort NameTypeList | ↑ds | ↑ts;

  // NTL → NT1 NTLT2

  // | NTL.ts = (NT1.t) ∥ NTLT2.ts
  ⟦ ⟨NameType#1↑t(#1t)⟩  ⟨NameTypeListTail#2↑ts(#2ts)⟩ ⟧ ↑ts(⟦ , ⟨Type#1t⟩ ⟨TypeListTail#2ts⟩ ⟧);

  // | NTL.ds = NT1.dst ∥ NTLT2.ds
  ⟦ ⟨NameType#1↑ds(#1ds)⟩  ⟨NameTypeListTail#2↑ds(#2ds)⟩ ⟧ ↑ds(AppendNameTypes(#1ds, #2ds));

  // NTL → ε

  // | NTL.ts = ε
  ⟦ ⟧ ↑ts(⟦⟧);

  // | NTL.ds = ε
  ⟦ ⟧ ↑ds(⟦⟧);
  
  // ----------
  // Rules for NTLT.
  sort NameTypeListTail | ↑ds | ↑ts;

  // NTLT → NT1 NTLT2

  // | NTLT.ts = (NT1.t) ∥ NTLT2.ts
  ⟦ , ⟨NameType#1↑t(#1t)⟩  ⟨NameTypeListTail#2↑ts(#2ts)⟩ ⟧ ↑ts(⟦ , ⟨Type#1t⟩ ⟨TypeListTail#2ts⟩ ⟧);

  // | NTLT.ds = NT1.dst ∥ NTLT2.ds
  ⟦ , ⟨NameType#1↑ds(#1ds)⟩  ⟨NameTypeListTail#2↑ds(#2ds)⟩ ⟧ ↑ds(AppendNameTypes(#1ds, #2ds));

  // NTLT → ε

  // | NTLT.ts = ε
  ⟦ ⟧ ↑ts(⟦⟧);

  // | NTLT.ds = ε
  ⟦ ⟧ ↑ds(⟦⟧);

  // ----------
  // Rules for NT
  sort NameType | ↑ds | ↑t;

  // NT → id1 : T2

  // | NT.t = T2
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟧ ↑t(#2);

  // | NT.ds = (⟨id1.sym, T2⟩)
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟧ ↑ds(⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟧);

  // ----------
  // Rules for Ss.
  sort Statements | scheme Sstert(Statements) ↓te ↓rt | ↑ok;

  | scheme SstertExtend(Statements, NameTypeListTail) ↓te ↓rt; // helper implementing Extend instance
  SstertExtend(#Ss, ⟦⟧) → Sstert(#Ss);
  SstertExtend(#Ss, ⟦ , ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟨NameTypeListTail#3⟩ ⟧)
    → SstertExtend(#Ss, #3) ↓te{#1 : #2};

  // Ss → S1 Ss2

  // | S1.te = Ss.te
  // | Ss2.te = Extend(Ss.te, S1.ds)
  // | S1.rt = Ss2.rt = S.rt
  Sstert(⟦ ⟨Statement#1↑ds(#1ds)⟩ ⟨Statements#2⟩ ⟧↑#syn)
    → ⟦ ⟨Statement Stert(#1)⟩ ⟨Statements SstertExtend(#2, #1ds)⟩ ⟧↑#syn;
  
  // | Ss.ok = S1.ok ∧ Ss2.ok
  ⟦ ⟨Statement#1↑ok(#1ok)⟩ ⟨Statements#2↑ok(#2ok)⟩ ⟧ ↑ok(And(#1ok, #2ok));

  // Ss → ε
  Sstert(⟦⟧↑#syn) → ⟦⟧↑#syn; //dummy

  // | Ss.ok = True
  ⟦⟧ ↑ok(True);

  // ----------
  // Rules for S.
  sort Statement | ↑ds | scheme Stert(Statement)↓te↓rt | ↑ok;
  | scheme Stert2(Statement) ↓te ↓rt; // helper to pass te and/or rt to subsequent dependency

  // S → { Ss1 }

  // | S.ds = ε
  ⟦ { ⟨Statements#1⟩ } ⟧ ↑ds(⟦⟧);

  // | Ss1.te = S.te
  // | Ss1.rt = S.rt
  Stert(⟦ { ⟨Statements#1⟩ } ⟧↑#syn) → ⟦ { ⟨Statements Sstert(#1)⟩ } ⟧↑#syn;

  // | S.ok = Ss1.ok
  ⟦ { ⟨Statements#1↑ok(#1ok)⟩ } ⟧ ↑ok(#1ok);
  
  // S → var NT1 ;
  
  // | S.ds = NT1.ds
  ⟦ var ⟨NameType#1↑ds(#1ds)⟩ ; ⟧ ↑ds(#1ds);

  // | S.ok = Eq(S.te, NT1.t, NT1.t)
  Stert(⟦ var ⟨NameType#1↑t(#1t)⟩ ; ⟧↑#syn) → ⟦ var ⟨NameType#1⟩ ; ⟧ ↑#syn ↑ok(Eq(#1t, #1t));

  // S → E1 ;

  // | S.ds = ε
  ⟦ ⟨Expression#1⟩ ; ⟧ ↑ds(⟦⟧);

  // | E1.te = S.te
  Stert(⟦ ⟨Expression#1⟩ ; ⟧↑#syn) → ⟦ ⟨Expression Ete(#1)⟩ ; ⟧↑#syn;

  // | S.ok = E1.ok;
  ⟦ ⟨Expression#1↑ok(#1ok)⟩ ; ⟧ ↑ok(#1ok);

  // S → ;
  Stert(⟦ ; ⟧↑#syn) → ⟦ ; ⟧↑#syn; //dummy

  // | S.ds = ε
  ⟦ ; ⟧ ↑ds(⟦⟧);
  
  // | S.ok = True
  ⟦ ; ⟧ ↑ok(True);

  // S → if ( E1 ) IT2

  // | S.ds = ε
  ⟦ if ( ⟨Expression#1⟩ ) ⟨IfTail#2⟩ ⟧ ↑ds(⟦⟧);

  // | E1.te = IT2.te = S.te
  // | IT2.rt = S.rt
  Stert(⟦ if ( ⟨Expression#1⟩ ) ⟨IfTail#2⟩ ⟧↑#syn)
    → Stert2(⟦ if ( ⟨Expression Ete(#1)⟩ ) ⟨IfTail ITtert(#2)⟩ ⟧↑#syn);

  // | S.ok = Eq(S.te, boolean, E1.t) ∧ E1.ok ∧ IT2.ok
  Stert2(⟦ if ( ⟨Expression#1↑t(#1t)↑ok(#1ok)⟩ ) ⟨IfTail#2↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ if ( ⟨Expression#1⟩ ) ⟨IfTail#2⟩ ⟧ ↑#syn
    ↑ok(And(Eq(⟦boolean⟧, #1t), And(#1ok, #2ok)));

  // S → while ( E1 ) S2

  // | S.ds = ε
  ⟦ while ( ⟨Expression#1⟩ ) ⟨Statement#2⟩ ⟧ ↑ds(⟦⟧);

  // | E1.te = S2.te = S.te
  // | S2.rt = S.rt
  Stert(⟦ while ( ⟨Expression#1⟩ ) ⟨Statement Stert(#2)⟩ ⟧↑#syn)
    → Stert2(⟦ while ( ⟨Expression Ete(#1)⟩ ) ⟨Statement Stert(#2)⟩ ⟧↑#syn);

  // | S.ok = Eq(S.te, boolean, E1.t) ∧ E1.ok ∧ S2.ok
  Stert2(⟦ while ( ⟨Expression#1↑t(#1t)↑ok(#1ok)⟩ ) ⟨Statement#2↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ while ( ⟨Expression#1⟩ ) ⟨Statement#2⟩ ⟧ ↑#syn
    ↑ok(And(Eq(⟦boolean⟧, #1t), And(#1ok, #2ok)));

  // S → return E1 ;

  // | S.ds = ε
  ⟦ return ⟨Expression#1⟩ ; ⟧ ↑ds(⟦⟧);

  // | E1.te = S.te
  Stert(⟦ return ⟨Expression#1⟩ ; ⟧↑#syn)
    → Stert2(⟦ return ⟨Expression Ete(#1)⟩ ; ⟧↑#syn);
  // | S.ok = E1.ok ∧ Eq(S.te, E1.t, S.rt)
  Stert2(⟦ return ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ ; ⟧↑#syn) ↓rt(#rt)
    → ⟦ return ⟨Expression#1⟩ ; ⟧ ↑#syn
    ↑ok(And(#1ok, Eq(#1t, #rt)));

  // S → return ;

  // | S.ds = ε
  ⟦ return ; ⟧ ↑ds(⟦⟧);

  // | S.ok = Eq(S.te, void, R.rt)
  Stert(⟦ return ; ⟧↑#syn) ↓rt(#rt) → ⟦ return ; ⟧ ↑#syn ↑ok(Eq(⟦void⟧, #rt));

  // ----------
  // Rules for IT.
  sort IfTail | scheme ITtert(IfTail)↓te↓rt  | ↑ok;

  // IT → S1 else S2
  
  // | S1.te = S2.te = IT.te
  // | S1.rt = S2.rt = IT.rt
  ITtert(⟦ ⟨Statement#1⟩ else ⟨Statement#2⟩ ⟧↑#syn)
    → ⟦ ⟨Statement Stert(#1)⟩ else ⟨Statement Stert(#2)⟩ ⟧ ↑#syn;

  // | IT.ok = S1.ok ∧ S2.ok
  ⟦ ⟨Statement#1↑ok(#1ok)⟩ else ⟨Statement#2↑ok(#2ok)⟩ ⟧ ↑ok(And(#1ok, #2ok));
  
  // IT → S1

  // | S1.te = IT.te
  // | S1.rt = IT.rt
  ITtert(⟦ ⟨Statement#1⟩ ⟧↑#syn)
    → ⟦ ⟨Statement Stert(#1)⟩ ⟧ ↑#syn;

  // | IT.ok = S1.ok
  ⟦ ⟨Statement#1↑ok(#1ok)⟩ ⟧ ↑ok(#1ok);

  // ----------
  // Rules for E.
  sort Expression | scheme Ete(Expression)↓te | ↑t | ↑ok;
  | scheme Ete2(Expression)↓te;  // carry E.te to t and ok synthesis

  // E → id1

  // | E.t = Lookup(E.te, id1.sym)
  // | E.ok = Defined(E.te, id1.sym)
  Ete(⟦ ⟨IDENTIFIER#1⟩ ⟧↑#syn) ↓te{¬#1} → ⟦ ⟨IDENTIFIER#1⟩ ⟧ ↑#syn ↑t(⟦void⟧) ↑ok(False);
  Ete(⟦ ⟨IDENTIFIER#1⟩ ⟧↑#syn) ↓te{#1:#1t} → ⟦ ⟨IDENTIFIER#1⟩ ⟧ ↑#syn ↑t(#1t) ↑ok(True);

  // E → str1
  Ete(⟦ ⟨STRING#1⟩ ⟧ ↑#syn) → ⟦ ⟨STRING#1⟩ ⟧↑#syn;
  
  // | E.t = string
  ⟦ ⟨STRING#1⟩ ⟧ ↑t(⟦string⟧);

  // | E.ok = True
  ⟦ ⟨STRING#1⟩ ⟧ ↑ok(True);

  // E → int1
  Ete(⟦ ⟨INTEGER#1⟩ ⟧ ↑#syn) → ⟦ ⟨INTEGER#1⟩ ⟧ ↑#syn;

  // | E.t = integer
  ⟦ ⟨INTEGER#1⟩ ⟧ ↑t(⟦integer⟧);

  // | E.ok = True
  ⟦ ⟨INTEGER#1⟩ ⟧ ↑ok(True);
  
  // E → E1 . id2

  // | E1.te = E.te
  Ete(⟦ ⟨Expression#1⟩ . ⟨IDENTIFIER#2⟩ ⟧↑#syn)
    → Ete2(⟦ ⟨Expression Ete(#1)⟩ . ⟨IDENTIFIER#2⟩ ⟧ ↑#syn);

  // | E.t = MemberType(E.te, E1.t, id2.sym)
  // | E.ok = E1.ok ∧ IsMember(E.te, E1.t, id2.sym)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ . ⟨IDENTIFIER#2⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ . ⟨IDENTIFIER#2⟩ ⟧ ↑#syn
    ↑t(MemberType(#1t, #2))
    ↑ok(And(#1ok, IsMember(#1t, #2)));
  
  // E → E1 ( EL2 )

  // | E1 .te = EL2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ ( ⟨ExpressionList#2⟩ ) ⟧↑#syn)
    → Ete2(⟦ ⟨Expression Ete(#1)⟩ ( ⟨ExpressionList ELte(#2)⟩ ) ⟧↑#syn);

  // | E.t = ReturnType(E1.t)
  // | E.ok = E1.ok ∧ IsMember(E.te, E1.t, id2.sym)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ ( ⟨ExpressionList#2 ↑ts(#2ts) ↑ok(#2ok)⟩ ) ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ ( ⟨Expression#2⟩ ) ⟧ ↑#syn
    ↑t(ReturnType(#1t))
    ↑ok(And(And(#1ok, #2ok), IsArguments(#1t, #2ts)));

  // E → ! E1

  // | E1.te = E.te
  Ete(⟦ ! ⟨Expression#1⟩ ⟧↑#syn) → Ete2(⟦ ! ⟨Expression Ete(#1)⟩ ⟧↑#syn);

  // | E.t = boolean
  // | E.ok = E1.ok ∧ Eq(E.te, boolean, E1.t)
  Ete2(⟦ ! ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ ⟧↑#syn)
    → ⟦ ! ⟨Expression#1⟩ ⟧ ↑#syn
    ↑t(⟦boolean⟧)
    ↑ok(And(#1ok, Eq(⟦boolean⟧, #1t)));

  // E → ~ E1

  // | E1.te = E.te
  Ete(⟦ ~ ⟨Expression#1⟩ ⟧↑#syn) → Ete2(⟦ ~ ⟨Expression Ete(#1)⟩ ⟧↑#syn);

  // | E.t = number
  // | E.ok = E1 ∧ Eq(E.te, number, E1.t)
  Ete2(⟦ ~ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ ⟧↑#syn)
    → ⟦ ~ ⟨Expression #1⟩ ⟧ ↑#syn
    ↑t(⟦number⟧)
    ↑ok(And(#1ok, Eq(⟦number⟧, #1t)));

  // E → - E1

  // | E1.te = E.te
  Ete(⟦ - ⟨Expression#1⟩ ⟧↑#syn) → Ete2(⟦ - ⟨Expression Ete(#1)⟩ ⟧↑#syn);

  // | E.t = number
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t)
  Ete2(⟦ - ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ ⟧↑#syn)
    → ⟦ - ⟨Expression #1⟩ ⟧ ↑#syn
    ↑t(⟦number⟧)
    ↑ok(And(#1ok, Eq(⟦number⟧, #1t)));

  // E → + E1

  // | E1.te = E.te
  Ete(⟦ + ⟨Expression#1⟩ ⟧↑#syn) → Ete2(⟦ + ⟨Expression Ete(#1)⟩ ⟧↑#syn);
  
  // | E.t = number
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t)
  Ete2(⟦ + ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ ⟧↑#syn)
    → ⟦ + ⟨Expression Ete(#1)⟩ ⟧ ↑#syn
    ↑t(⟦number⟧)
    ↑ok(And(#1ok, Eq(⟦number⟧, #1t)));

  // E → E1 * E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ * ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ * ⟨Expression Ete(#2)⟩ ⟧↑#syn);
  
  // | E.t = number
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t) ∧ E2.ok ∧ Eq(E.te, number, E2.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ * ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ * ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦number⟧)
    ↑ok(And(And(#1ok, Eq(⟦number⟧, #1t)), And(#2ok, Eq(⟦number⟧, #2t))));

  // E → E1 / E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ / ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ / ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = number
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t) ∧ E2.ok ∧ Eq(E.te, number, E2.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ / ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ / ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦number⟧)
    ↑ok(And(And(#1ok, Eq(⟦number⟧, #1t)), And(#2ok, Eq(⟦number⟧, #2t))));

  // E → E1 % E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ % ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ % ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = number
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t) ∧ E2.ok ∧ Eq(E.te, number, E2.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ % ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ % ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦number⟧)
    ↑ok(And(And(#1ok, Eq(⟦number⟧, #1t)), And(#2ok, Eq(⟦number⟧, #2t))));

  // E → E1 + E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ + ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ + ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = if (Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t)) then number else string
  // | E.ok = E1.ok ∧ E2.ok
  //       ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  //       ∧ (Eq(E.te, number, E2.t) ∨ Eq(E.te, string, E2.t))
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ + ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ + ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(IfType(And(Eq(⟦number⟧, #1t), Eq(⟦number⟧, #2t)), ⟦number⟧, ⟦string⟧))
    ↑ok(And(
	And(#1ok, #2ok),
	And(
	    Or(Eq(⟦number⟧, #1t), Eq(⟦string⟧, #1t)),
	    Or(Eq(⟦number⟧, #2t), Eq(⟦string⟧, #2t)))));
  
  // E → E1 - E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ - ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ - ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = number
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t) ∧ E2.ok ∧ Eq(E.te, number, E2.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ - ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ - ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦number⟧)
    ↑ok(And(And(#1ok, Eq(⟦number⟧, #1t)), And(#2ok, Eq(⟦number⟧, #2t))));

  // E → E1 <= E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ <= ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ <= ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = boolean
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ <= ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ <= ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦boolean⟧)
    ↑ok(And(And(#1ok, #2ok), And(Eq(#1t, #2t), Or(Eq(⟦number⟧, #1t), Eq(⟦string⟧, #1t)))));

  // E → E1 >= E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ >= ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ >= ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = boolean
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ >= ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ >= ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦boolean⟧)
    ↑ok(And(And(#1ok, #2ok), And(Eq(#1t, #2t), Or(Eq(⟦number⟧, #1t), Eq(⟦string⟧, #1t)))));

  // E → E1 < E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ < ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ < ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = boolean
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ < ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ < ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦boolean⟧)
    ↑ok(And(And(#1ok, #2ok), And(Eq(#1t, #2t), Or(Eq(⟦number⟧, #1t), Eq(⟦string⟧, #1t)))));

  // E → E1 > E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ > ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ > ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = boolean
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ > ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ > ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦boolean⟧)
    ↑ok(And(And(#1ok, #2ok), And(Eq(#1t, #2t), Or(Eq(⟦number⟧, #1t), Eq(⟦string⟧, #1t)))));

  // E → E1 == E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ == ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ == ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = boolean
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ == ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ == ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦boolean⟧)
    ↑ok(And(And(#1ok, #2ok), Eq(#1t, #2t)));

  // E → E1 != E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ != ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ != ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = boolean
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ != ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ != ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦boolean⟧)
    ↑ok(And(And(#1ok, #2ok), Eq(#1t, #2t)));

  // E → E1 & E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ & ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ & ⟨Expression Ete(#2)⟩ ⟧↑#syn);
  
  // | E.t = number
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t) ∧ E2.ok ∧ Eq(E.te, number, E2.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ & ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ & ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦number⟧)
    ↑ok(And(And(#1ok, Eq(⟦number⟧, #1t)), And(#2ok, Eq(⟦number⟧, #2t))));

  // E → E1 | E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ | ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ | ⟨Expression Ete(#2)⟩ ⟧↑#syn);
  
  // | E.t = number
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t) ∧ E2.ok ∧ Eq(E.te, number, E2.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ | ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ | ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦number⟧)
    ↑ok(And(And(#1ok, Eq(⟦number⟧, #1t)), And(#2ok, Eq(⟦number⟧, #2t))));

  // E → E1 && E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ && ⟨Expression#2⟩ ⟧↑#syn) → Ete2(⟦ ⟨Expression Ete(#1)⟩ && ⟨Expression Ete(#2)⟩ ⟧↑#syn);
  
  // | E.t = boolean
  // | E.ok = E1.ok ∧ Eq(E.te, boolean, E1.t) ∧ E2.ok ∧ Eq(E.te, boolean, E2.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ && ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ && ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦boolean⟧)
    ↑ok(And(And(#1ok, Eq(⟦boolean⟧, #1t)), And(#2ok, Eq(⟦boolean⟧, #2t))));

  // E → E1 || E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ || ⟨Expression#2⟩ ⟧↑#syn)
    → Ete2(⟦ ⟨Expression Ete(#1)⟩ || ⟨Expression Ete(#2)⟩ ⟧↑#syn);
  
  // | E.t = boolean
  // | E.ok = E1.ok ∧ Eq(E.te, boolean, E1.t) ∧ E2.ok ∧ Eq(E.te, boolean, E2.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ || ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ || ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(⟦boolean⟧)
    ↑ok(And(And(#1ok, Eq(⟦boolean⟧, #1t)), And(#2ok, Eq(⟦boolean⟧, #2t))));

  // E → E1 ? E2 : E3

  // | E1.te = E2.te = E3.te = E.te
  Ete(⟦ ⟨Expression#1⟩ ? ⟨Expression#2⟩ : ⟨Expression#3⟩ ⟧↑#syn)
    → Ete2(⟦ ⟨Expression Ete(#1)⟩ ? ⟨Expression Ete(#2)⟩ : ⟨Expression Ete(#3)⟩ ⟧↑#syn);
  
  // | E.t = E2.t
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, boolean, E1.t) ∧ E3.ok ∧ Eq(E.te, E2.t, E3.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ ? ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ : ⟨Expression#3 ↑t(#3t) ↑ok(#3ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ ? ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ : ⟨Expression#3 ↑t(#3t) ↑ok(#3ok)⟩ ⟧ ↑#syn
    ↑t(#2t)
    ↑ok(And(And(#1ok, Eq(⟦boolean⟧, #1t)), And(And(#2ok, #3ok), Eq(#2t, #3t))));

  // E → E1 = E2

  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ = ⟨Expression#2⟩ ⟧↑#syn)
    → Ete2(⟦ ⟨Expression Ete(#1)⟩ = ⟨Expression Ete(#2)⟩ ⟧↑#syn);
  
  // | E.t = E1.t
  // | E.ok = IsLValue(E1) ∧ E1.ok ∧ E2.ok ∧ Eq(E.te, E1.t, E2.t)
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ = ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ = ⟨Expression#2⟩ ⟧ ↑#syn
    ↑t(#1t)
    ↑ok(And(
	    And(IsLValue(#1), And(#1ok, #2ok)),
	    Or(And(Eq(⟦number⟧, #1t), Eq(⟦number⟧, #2t)),
	       And(Eq(⟦string⟧, #1t),
		   Or(Eq(⟦string⟧, #2t), Eq(⟦number⟧, #2t))))));

  // E → E1 += E2
  
  // | E1.te = E2.te = E.te
  Ete(⟦ ⟨Expression#1⟩ += ⟨Expression#2⟩ ⟧↑#syn)
    → Ete2(⟦ ⟨Expression Ete(#1)⟩ += ⟨Expression Ete(#2)⟩ ⟧↑#syn);

  // | E.t = E1.t
  // | E.ok = IsLValue(E1) ∧ E1.ok ∧ E2.ok
  //    ∧ ((Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t))
  //        ∨ (Eq(E.te, string, E1.t)
  //             ∧ (Eq(E.te, string, E2.t) ∨ Eq(E.te, number, E2.t))))
  Ete2(⟦ ⟨Expression#1 ↑t(#1t) ↑ok(#1ok)⟩ += ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn)
    → ⟦⟨Expression#1⟩ += ⟨Expression#2⟩ ⟧↑#syn
    ↑t(#1t)
    ↑ok(Or(
	   And(And(IsLValue(#1), And(#1ok, #2ok)), And(Eq(⟦number⟧, #1t), Eq(⟦number⟧, #2t))),
	   And(Eq(⟦string⟧, #1t), Or(Eq(⟦string⟧, #2t), Eq(⟦number⟧, #2t)))));

  // E → E1 = { KVL2 }

  // | E1.te = E.te
  Ete(⟦ ⟨Expression#1⟩ = { ⟨KeyValueList#2⟩ } ⟧↑#syn)
    → Ete2(⟦ ⟨Expression Ete(#1)⟩ = { ⟨KeyValueList#2⟩ } ⟧↑#syn);

  // | E.t = E1.t
  ⟦ ⟨Expression#1↑t(#1t)⟩ = { ⟨KeyValueList#2⟩ } ⟧ ↑t(#1t);

  // | KVL2.te = E.te
  // | KVL2.mt = E1.t
  // | KVL2.ids = RecordNames(E.te, E1.t)
  Ete2(⟦ ⟨Expression#1↑t(#1t)⟩ = { ⟨KeyValueList#2⟩ } ⟧↑#syn)
    → ⟦ ⟨Expression#1⟩ = { ⟨KeyValueList KVLtemtids(#2) ↓mt(#1t) ↓ids(RecordNames(#1t))⟩ } ⟧↑#syn;
  
  // | E.ok = IsLValue(E1) ∧ E1.ok ∧ KVL2.ok
  ⟦ ⟨Expression#1↑ok(#1ok)⟩ = { ⟨KeyValueList#2↑ok(#2ok)⟩ } ⟧
    ↑ok(And(IsLValue(#1), And(#1ok, #2ok)));
  
  // ----------
  // Rules for EL.
  sort ExpressionList | scheme ELte(ExpressionList)↓te | ↑ts | ↑ok;
    
  // EL → E1 ELT2

  // | E1.te = ELT2.te = EL.te
  ELte(⟦ ⟨Expression#1⟩ ⟨ExpressionListTail#2⟩ ⟧↑#syn)
    → ⟦ ⟨Expression Ete(#1)⟩ ⟨ExpressionListTail ELTte(#2)⟩ ⟧↑#syn;

  // | EL.ts = (E1.ts) ∥ ELT2.ts
  ⟦ ⟨Expression#1↑t(#1t)⟩ ⟨ExpressionListTail#2↑ts(#2ts)⟩ ⟧
    ↑ts(⟦, ⟨Type#1t⟩ ⟨TypeListTail#2ts⟩ ⟧);

  // EL.ok = E1.ok ∧ ELT2.ok
  ⟦ ⟨Expression#1↑ok(#1ok)⟩ ⟨ExpressionListTail#2↑ok(#2ok)⟩ ⟧
    ↑ok(And(#1ok, #2ok));

  // EL → ε
  ELte(⟦⟧↑#syn) → ⟦⟧↑#syn; //dummy

  // EL.ts = ε
  ⟦⟧ ↑ts(⟦⟧);

  // EL.ok = True
  ⟦⟧ ↑ok(True);

  // ----------
  // Rules for ELT.
  sort ExpressionListTail | scheme ELTte(ExpressionListTail)↓te | ↑ts | ↑ok;

  // ELT → E1 ELT2

  // | E1.te = ELT2.te = ELT.te
  ELTte(⟦ , ⟨Expression#1⟩ ⟨ExpressionListTail#2⟩ ⟧↑#syn)
    → ⟦ , ⟨Expression Ete(#1)⟩ ⟨ExpressionListTail ELTte(#2)⟩ ⟧↑#syn;

  // | ELT.ts = (E1.ts) ∥ ELT2.ts
  ⟦ , ⟨Expression#1↑t(#1t)⟩ ⟨ExpressionListTail#2↑ts(#2ts)⟩ ⟧
    ↑ts(⟦, ⟨Type#1t⟩ ⟨TypeListTail#2ts⟩ ⟧);

  // ELT.ok = E1.ok ∧ ELT2.ok
  ⟦ , ⟨Expression#1↑ok(#1ok)⟩ ⟨ExpressionListTail#2↑ok(#2ok)⟩ ⟧
    ↑ok(And(#1ok, #2ok));

  // ELT → ε
  ELTte(⟦⟧↑#syn) → ⟦⟧↑#syn;

  // ELT.ts = ε
  ⟦⟧ ↑ts(⟦⟧);

  // ELT.ok = True
  ⟦⟧ ↑ok(True);

  // ----------
  // Rules for KVL.
  sort KeyValueList | scheme KVLtemtids(KeyValueList)↓te↓mt↓ids | scheme KVLids2(KeyValueList)↓ids | ↑ok;

  // KVL → KV1 KVLT2

  // | KV1.te = KVLT2.te = KVL .te
  // | KV1.mt = KVLT2.mt = KVL.mt
  // | KVLT2.ids = KVL.ids \ KV1.id
  KVLtemtids(⟦ ⟨KeyValue#1↑id(#1id)⟩ ⟨KeyValueListTail#2⟩ ⟧↑#syn) ↓ids(#ids)
    → KVLids2(⟦ ⟨KeyValue KVtemt(#1)⟩ ⟨KeyValueListTail KVLTtemtids(#2) ↓ids(NamesBut(#ids, #1id))⟩ ⟧↑#syn);

  // | KVL.ok = KV1.ok ∧ KV1.id ∈ KVL.ids ∧ KVLT2.ok
  KVLids2(⟦ ⟨KeyValue#1↑id(#1id)↑ok(#1ok)⟩ ⟨KeyValueListTail#2↑ok(#2ok)⟩ ⟧↑#syn) ↓ids(#ids)
    → ⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧↑#syn
    ↑ok(And(InNames(#1id, #ids), And(#1ok, #2ok)));

  // KVL → ε

  // | KVL.ok = OnlyFunctions(KVL.te, KVL.mt, KVL.ids)
  KVLtemtids(⟦⟧↑#syn) ↓ids(#ids) → ⟦⟧ ↑#syn ↑ok(OnlyFunctions(#ids));

  // ----------
  // Rules for KVLT.
  sort KeyValueListTail | scheme KVLTtemtids(KeyValueListTail)↓te↓mt↓ids | scheme KVLTids2(KeyValueListTail)↓ids | ↑ok;

  // KVLT → KV1 KVLT2

  // | KV1.te = KVLT2.te = KVLT .te
  // | KV1.mt = KVLT2.mt = KVLT.mt
  // | KVLT2.ids = KVLT.ids \ KV1.id
  KVLTtemtids(⟦ , ⟨KeyValue#1↑id(#1id)⟩ ⟨KeyValueListTail#2⟩ ⟧↑#syn) ↓ids(#ids)
    → KVLTids2(⟦ , ⟨KeyValue KVtemt(#1)⟩ ⟨KeyValueListTail KVLTtemtids(#2) ↓ids(NamesBut(#ids, #1id))⟩ ⟧↑#syn);

  // | KVLT.ok = KV1.ok ∧ KV1.id ∈ KVLT.ids ∧ KVLT2.ok
  KVLTids2(⟦ , ⟨KeyValue#1↑id(#1id)↑ok(#1ok)⟩ ⟨KeyValueListTail#2↑ok(#2ok)⟩ ⟧↑#syn) ↓ids(#ids)
    → ⟦ , ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧↑#syn
    ↑ok(And(InNames(#1id, #ids), And(#1ok, #2ok)));

  // KVLT → ε

  // | KVLT.ok = OnlyFunctions(KVLT.te, KVLT.mt, KVLT.ids)
  KVLTtemtids(⟦⟧↑#syn) ↓ids(#ids) → ⟦⟧ ↑#syn ↑ok(OnlyFunctions(#ids));

  // ----------
  // Rules for KV.
  sort KeyValue | ↑id | scheme KVtemt(KeyValue)↓te↓mt | ↑ok;
  | scheme KVtemt2(KeyValue)↓te↓mt; // for assembling ok after te propagated
  
  // KV → id1 : E2
  
  // | KV.id = id1.sym
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧ ↑id(#1);

  // | E2.te = KV.te
  KVtemt(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧↑#syn)
    → KVtemt2(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression Ete(#2)⟩ ⟧↑#syn);
  
  // | KV.ok = E2.ok ∧ Eq(KV.te, Lookup(KV.mt, id1.sym), E2.t)
  KVtemt2(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2 ↑t(#2t) ↑ok(#2ok)⟩ ⟧↑#syn) ↓mt(#mt)
    → ⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧↑#syn
    ↑ok(And(#2ok, Eq(#2t, MemberType(#mt, #1))));
  
  // [2]1.11. SEMANTIC OPERATORS

  // * GlobalDefs
  sort NameTypeListTail | scheme GlobalDefs;
  GlobalDefs → ⟦
    , document : {body : {innerHTML : string}}
    , length : (string) => number
    , charAt : (string, number) => number
    , substr : (string, number, number) => string
    ⟧;
  
  // * OnlyFunctions(te, mt, ids)
  sort Bool | scheme OnlyFunctions(Names)↓te↓mt;
  OnlyFunctions(NamesNil) → True;
  OnlyFunctions(NamesCons(#id, #rest)) ↓mt(#mt)
    → And(IsFunctionType(MemberType(#mt, #id)), OnlyFunctions(#rest)↓mt(#mt));
  | scheme IsFunctionType(Type) | scheme IsFunctionType2(Type);
  [data #] IsFunctionType(#) → IsFunctionType2(#);
  IsFunctionType2(⟦ ( ⟨TypeList#1⟩ ) => ⟨Type#2⟩ ⟧) → True;
  default IsFunctionType2(#) → False;

  // * DistinctFirst(kvs)
  attribute ↓used{IDENTIFIER};
  sort Bool | scheme DistinctFirst(NameTypeListTail) ↓used | scheme DistinctFirst2(NameTypeListTail) ↓used;
  [data #] DistinctFirst(#) → DistinctFirst2(#);
  DistinctFirst2(⟦⟧) → True;
  DistinctFirst2(⟦ , ⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#2⟩ ⟧) ↓used{¬#11}
    → DistinctFirst2(#2) ↓used{#11};
  DistinctFirst2(⟦ , ⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#2⟩ ⟧) ↓used{#11}
    → False;

  // * Eq(te, T1, T2)
  sort Bool | scheme Eq(Type, Type)↓te;
  Eq(#1,#2) → True;
  //  - Identifier combinations
  priority Eq(⟦ ⟨IDENTIFIER#1⟩ ⟧, ⟦ ⟨IDENTIFIER#1⟩ ⟧) → True;
  Eq(⟦ ⟨IDENTIFIER#1⟩ ⟧, #2) → Eq(ResolveType(#1), #2);
  Eq(#1, ⟦ ⟨IDENTIFIER#2⟩ ⟧) → Eq(#1, ResolveType(#2));
  //  - Simple type cases.
  Eq(⟦boolean⟧, ⟦boolean⟧) → True;
  Eq(⟦number⟧, ⟦number⟧) → True;
  Eq(⟦string⟧, ⟦string⟧) → True;
  Eq(⟦void⟧, ⟦void⟧) → True;
  Eq(⟦ ( ⟨TypeList#11⟩ ) => ⟨Type#12⟩ ⟧, ⟦ ( ⟨TypeList#21⟩ ) => ⟨Type#22⟩ ⟧)
    → And(Eqs(TailTypes(#11), TailTypes(#21)), Eq(#12, #22));
  Eq(⟦ { ⟨NameTypeList#1⟩ } ⟧, ⟦ { ⟨NameTypeList#2⟩ } ⟧)
    → EqNTLT(#1, #2);
  //  - Fallback.
  default Eq(#1, #2) → False;

  //  - helper for lists of types...
  | scheme Eqs(TypeListTail, TypeListTail)↓te;
  Eqs(⟦⟧, ⟦⟧) → True;
  Eqs(⟦ , ⟨Type#11⟩ ⟨TypeListTail#12⟩ ⟧, ⟦ , ⟨Type#21⟩ ⟨TypeListTail#22⟩ ⟧)
    → And(Eq(#11, #21), Eqs(#12, #22));

  //  - helper for record content...
  | scheme EqNTLT(NameTypeListTail, NameTypeListTail)↓te;
  EqNTLT(⟦⟧, ⟦⟧) → True;
  EqNTLT(⟦ , ⟨IDENTIFIER#id⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#13⟩ ⟧, ⟦ , ⟨IDENTIFIER#id⟩ : ⟨Type#22⟩ ⟨NameTypeListTail#23⟩ ⟧)
    → And(Eq(#12, #22), EqNTLT(#13, #23));
  default EqNTLT(⟦ , ⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#13⟩ ⟧, ⟦ , ⟨IDENTIFIER#21⟩ : ⟨Type#22⟩ ⟨NameTypeListTail#23⟩ ⟧)
    → EqNTLT(#13, #23);
  default EqNTLT(⟦⟧, #) → False;
  default EqNTLT(#, ⟦⟧) → False;

  // * IsMember(te, T, id)
  sort Bool | scheme IsMember(Type, IDENTIFIER) ↓te;
  IsMember(⟦ ⟨IDENTIFIER#1⟩ ⟧, #2) ↓te{#1 : #t} → IsMember(#t, #2);
  IsMember(⟦ { ⟨NameTypeList#1⟩ } ⟧, #2) → IsMember2(TailNameTypes(#1), #2);
  default IsMember(#, #2) → False;
  | scheme IsMember2(NameTypeListTail, IDENTIFIER);
  IsMember2(⟦⟧, #2) → False;
  IsMember2(⟦ , ⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#13⟩ ⟧, #11) → True;
  default IsMember2(⟦ , ⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#13⟩ ⟧, #2)
    → IsMember2(#13, #2);

  // * MemberType(te, T, id)
  sort Type | scheme MemberType(Type, IDENTIFIER) ↓te;
  MemberType(⟦ ⟨IDENTIFIER#1⟩ ⟧, #2) ↓te{#1 : #t} → MemberType(#t, #2);
  MemberType(⟦ { ⟨NameTypeList#1⟩ } ⟧, #2) → MemberType2(TailNameTypes(#1), #2);
  default MemberType(#, #2) → ⟦ {} ⟧;
  | scheme MemberType2(NameTypeListTail, IDENTIFIER);
  MemberType2(⟦⟧, #2) → ⟦ {} ⟧;
  MemberType2(⟦ , ⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#13⟩ ⟧, #11) → #12;
  default MemberType2(⟦ , ⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#13⟩ ⟧, #2)
    → MemberType2(#13, #2);
  
  // * IsArguments(te, t:T, ts:TL)
  sort Bool | scheme IsArguments(Type, TypeListTail) ↓te;
  IsArguments(⟦ ( ⟨TypeList#11⟩ ) => ⟨Type#12⟩ ⟧, #2) → Eqs(TailTypes(#11), #2);
  default IsArguments(#1, #2) → False;

  // * ReturnType(T)
  sort Type | scheme ReturnType(Type);
  ReturnType(⟦ ( ⟨TypeList#1⟩ ) => ⟨Type#2⟩ ⟧) → #2;
  default ReturnType(#) → ⟦void⟧;

  // * IsLValue(E).
  sort Bool | scheme IsLValue(Expression);
  IsLValue(⟦⟨IDENTIFIER#1⟩⟧) → True;
  IsLValue(⟦⟨Expression#1⟩.⟨IDENTIFIER#2⟩⟧) → True;
  default IsLValue(#) → False;

  // * RecordNames(te, T)
  sort Names | scheme RecordNames(Type)↓te | scheme RecordNames2(Type)↓te;
  [data #] RecordNames(#) → RecordNames2(#);
  RecordNames2(⟦ ⟨IDENTIFIER#1⟩ ⟧) → RecordNames(ResolveType(#1));
  RecordNames2(⟦ { ⟨NameTypeList#1⟩ } ⟧) → NameTypeNames(TailNameTypes(#1));
  default RecordNames2(#) → NamesNil;

  // * Names(te, TLT)
  sort Names | scheme NameTypeNames(NameTypeListTail);
  NameTypeNames(⟦ , ⟨IDENTIFIER#11⟩ : ⟨Type#12⟩ ⟨NameTypeListTail#2⟩ ⟧)
    → NamesCons(#11, NameTypeNames(#2));
  NameTypeNames(⟦⟧) → NamesNil;

  // * ResolveType(te, id)
  sort Type | scheme ResolveType(IDENTIFIER)↓te;
  ResolveType(#id) ↓te{#id : #t} → #t ;
  ResolveType(#id) ↓te{¬#id} → ⟦ {} ⟧;

  // * IfType(test, T1, T2)
  sort Type | scheme IfType(Bool, Type, Type);
  IfType(True, #1, #2) → #1;
  IfType(False, #1, #2) → #2;
  
  
  ////////////////////////////////////////////////////////////////////////
  // MAIN.

  sort Result | ⟦OK⟧ | ⟦TYPE ERROR⟧;
  | scheme Check(Program);
  Check(#P) → Check2(P2(#P));

  | scheme Check2(Program);
  Check2(#P ↑ok(True)) → ⟦OK⟧;
  Check2(#P ↑ok(False)) → ⟦TYPE ERROR⟧;
  
}
