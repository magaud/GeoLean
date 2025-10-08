import GeoLean.theories.Axioms.tarski_axioms

section Definitions

variable {Tn:Tarski_neutral_dimensionless} --{TPoint:Type} {Bet:TPoint->TPoint->TPoint->Prop} {Cong:TPoint->TPoint->TPoint->TPoint->Prop}
open Tarski_neutral_dimensionless
/-- Definition 2.10. -/

def OFSC A B C D A' B' C' D' :=
  Bet A B C /\ Bet A' B' C' /\
  Cong A B A' B' /\ Cong B C B' C' /\
  Cong A D A' D' /\ Cong B D B' D'

/-- Definition 3.8. -/

def Bet_4 A1 A2 A3 A4 :=
   Bet A1 A2 A3 /\ Bet A2 A3 A4 /\ Bet A1 A3 A4 /\ Bet A1 A2 A4

/-- Definition 4.1. -/

def IFSC A B C D A' B' C' D' :=
   Bet A B C /\ Bet A' B' C' /\
   Cong A C A' C' /\ Cong B C B' C' /\
   Cong A D A' D' /\ Cong C D C' D'

/-- Definition 4.4. -/

def Cong_3 A B C A' B' C' :=
  Cong A B A' B' /\ Cong A C A' C' /\ Cong B C B' C'

def Cong_4 P1 P2 P3 P4 Q1 Q2 Q3 Q4 :=
  Cong P1 P2 Q1 Q2 /\ Cong P1 P3 Q1 Q3 /\ Cong P1 P4 Q1 Q4 /\
  Cong P2 P3 Q2 Q3 /\ Cong P2 P4 Q2 Q4 /\ Cong P3 P4 Q3 Q4

def Cong_5 P1 P2 P3 P4 P5 Q1 Q2 Q3 Q4 Q5 :=
  Cong P1 P2 Q1 Q2 /\ Cong P1 P3 Q1 Q3 /\
  Cong P1 P4 Q1 Q4 /\ Cong P1 P5 Q1 Q5 /\
  Cong P2 P3 Q2 Q3 /\ Cong P2 P4 Q2 Q4 /\ Cong P2 P5 Q2 Q5 /\
  Cong P3 P4 Q3 Q4 /\ Cong P3 P5 Q3 Q5 /\ Cong P4 P5 Q4 Q5

/-- Definition 4.10. -/

def Col A B C  := Bet A B C \/ Bet B C A \/ Bet C A B

/-- Definition 4.15. -/

def FSC A B C D A' B' C' D' :=
  Col A B C /\ Cong_3 A B C A' B' C' /\ Cong A D A' D' /\ Cong B D B' D'

/-- Definition 5.4. -/

def Le A B C D := exists E, Bet C E D /\ Cong A B C E

def Ge A B C D := Le C D A B

/-- Definition 5.14. -/

def Lt A B C D := Le A B C D /\ ¬ Cong A B C D

def Gt A B C D := Lt C D A B

/-- Definition 6.1. -/

def Out P A B := A ≠ P /\ B ≠ P /\ (Bet P A B \/ Bet P B A)

/-- Definition 6.22. -/

def Inter2 A1 A2 B1 B2 X :=  -- renamed because Inter already exists
 B1 ≠ B2 /\ (exists P, Col P B1 B2 /\ ¬ Col P A1 A2) /\
 Col A1 A2 X /\ Col B1 B2 X

/-- Definition 7.1. -/

def Midpoint M A B := Bet A M B /\ Cong A M M B

/-- Definition 8.1. -/

def Per A B C := exists C', Midpoint B C C' /\ Cong A C A C'

/-- Definition 8.11. -/

def Perp_at (X A B C D:Tpoint) :=
  A ≠ B /\ C ≠ D /\ Col X A B /\ Col X C D /\
  forall U V, Col U A B -> Col V C D -> Per U X V

/-- Definition 8.11. -/

def Perp (A B C D:Tpoint) := exists X, Perp_at X A B C D

/-- Definition 9.1. -/

def TS A B P Q :=
  ¬ Col P A B /\ ¬ Col Q A B /\ exists T, Col T A B /\ Bet P T Q

/-- Definition 9.7. -/

def OS (A B P Q:Tpoint) := exists R, TS A B P R /\ TS A B Q R

/-- Satz 9.33. -/

def Coplanar A B C D :=
  exists X, (Col A B X /\ Col C D X) \/
            (Col A C X /\ Col B D X) \/
            (Col A D X /\ Col B C X)

/-- Definition 9.37 -/

def TSP A B C P Q :=
  ¬ Coplanar A B C P /\ ¬ Coplanar A B C Q /\ (exists T, Coplanar A B C T /\ Bet P T Q)

/-- Definition 9.40 -/

def OSP (A B C P Q:Tpoint) :=
  exists R, TSP A B C P R /\ TSP A B C Q R

/-- Definition 10.3. -/

def ReflectL P' P A B :=
  (exists X, Midpoint X P P' /\ Col A B X) /\ (Perp A B P P' \/ P = P')

def Reflect (P' P A B:Tpoint) :=
 (A ≠ B /\ ReflectL P' P A B) \/ (A = B /\ Midpoint A P P')

def ReflectL_at (M P' P A B:Tpoint) :=
  (Midpoint M P P' /\ Col A B M) /\ (Perp A B P P' \/ P = P')

def Reflect_at (M P' P A B:Tpoint) :=
 (A ≠ B /\ ReflectL_at M P' P A B) \/ (A = B /\ A = M /\ Midpoint M P P')

/-- Definition 11.2. -/

def CongA A B C D E F :=
  A ≠ B /\ C ≠ B /\ D ≠ E /\ F ≠ E /\
  exists A', exists C', exists D', exists F',
  Bet B A A' /\ Cong A A' E D /\
  Bet B C C' /\ Cong C C' E F /\
  Bet E D D' /\ Cong D D' B A /\
  Bet E F F' /\ Cong F F' B C /\
  Cong A' C' D' F'

/-- Definition 11.23. -/

def InAngle P A B C :=
  A ≠ B /\ C ≠ B /\ P ≠ B /\ exists X, Bet A X C /\ (X = B \/ Out B X P)

/-- Definition 11.27. -/

def LeA A B C D E F := exists P, InAngle P D E F /\ CongA A B C D E P

def GeA A B C D E F := LeA D E F A B C

/-- Definition 11.38. -/

def LtA (A B C D E F:Tpoint) := LeA A B C D E F /\ ¬ CongA A B C D E F

def GtA A B C D E F := LtA D E F A B C

/-- Definition 11.39. -/

def Acute (A B C:Tpoint) :=
  exists A' B' C', Per A' B' C' /\ LtA A B C A' B' C'

/-- Definition 11.39. -/

def Obtuse (A B C:Tpoint) :=
  exists A' B' C', Per A' B' C' /\ LtA A' B' C' A B C

/-- Definition 11.59. -/

def Orth_at X A B C U V :=
  ¬ Col A B C /\ U ≠ V /\ Coplanar A B C X /\ Col U V X /\
  forall P Q, Coplanar A B C P -> Col U V Q -> Per P X Q

def Orth (A B C U V:Tpoint) := exists X, Orth_at X A B C U V

/-- Definition 12.2. -/

def Par_strict (A B C D:Tpoint) :=
  Coplanar A B C D /\  ¬exists X, Col X A B /\ Col X C D

/-- Definition 12.3. -/

def Par (A B C D:Tpoint) :=
  Par_strict A B C D \/ (A ≠ B /\ C ≠ D /\ Col A C D /\ Col B C D)

/-- Definition 13.4. -/

def Q_Cong (l: Tpoint -> Tpoint -> Prop) := exists A B, forall (X Y:Tpoint), Cong A B X Y <-> l X Y

def Len (A B:Tpoint) l := Q_Cong l /\ l A B

def Q_Cong_Null (l:Tpoint -> Tpoint -> Prop) := Q_Cong l /\ exists A, l A A

def EqL (l1 l2 : Tpoint -> Tpoint -> Prop) :=
  forall A B, l1 A B <-> l2 A B

def Q_CongA (a: Tpoint -> Tpoint -> Tpoint -> Prop):=
  exists A B C,
    A ≠ B /\ C ≠ B /\ forall X Y Z, CongA A B C X Y Z <-> a X Y Z

def Ang A B C a := Q_CongA a /\ a A B C

def Ang_Flat a := Q_CongA a /\ forall A B C, a A B C -> Bet A B C

def EqA (a1 a2 : Tpoint -> Tpoint -> Tpoint -> Prop) :=
  forall A B C, a1 A B C <-> a2 A B C

/-- Definition 13.9. -/

def Perp2 A B C D P :=
  exists X Y, Col P X Y /\ Perp X Y A B /\ Perp X Y C D

def Q_CongA_Acute (a:Tpoint -> Tpoint -> Tpoint -> Prop) :=
  exists A B C,
    Acute A B C /\ forall X Y Z, CongA A B C X Y Z <-> a X Y Z

def Ang_Acute A B C (a:Tpoint -> Tpoint -> Tpoint -> Prop) := Q_CongA_Acute a /\ a A B C

def Q_CongA_nNull (a:Tpoint -> Tpoint -> Tpoint -> Prop) := Q_CongA a /\ forall A B C, a A B C -> ¬ Out B A C

def Q_CongA_nFlat (a:Tpoint -> Tpoint -> Tpoint -> Prop) := Q_CongA a /\ forall A B C, a A B C -> ¬ Bet A B C

def Q_CongA_Null (a:Tpoint -> Tpoint -> Tpoint -> Prop) := Q_CongA a /\ forall A B C, a A B C -> Out B A C

def Q_CongA_Null_Acute (a:Tpoint -> Tpoint -> Tpoint -> Prop) :=
  Q_CongA_Acute a /\ forall A B C, a A B C -> Out B A C

def is_null_anga' (a:Tpoint -> Tpoint -> Tpoint -> Prop) :=
  Q_CongA_Acute a /\ exists A B C, a A B C /\ Out B A C

def Q_CongA_nNull_Acute (a:Tpoint -> Tpoint -> Tpoint -> Prop) :=
  Q_CongA_Acute a /\ forall A B C, a A B C ->  ¬ Out B A C

def Lcos lb lc a :=
  Q_Cong lb /\ Q_Cong lc /\ Q_CongA_Acute a /\
  (exists A B C, (Per C B A /\ lb A B /\ lc A C /\ a B A C))

def Eq_Lcos (la:Tpoint -> Tpoint -> Prop)
            (a:Tpoint -> Tpoint -> Tpoint -> Prop)
            (lb:Tpoint -> Tpoint -> Prop)
            (b:Tpoint -> Tpoint -> Tpoint -> Prop) := exists lp, Lcos lp la a /\ Lcos lp lb b

def Lcos2 lp l a b := exists la, Lcos la l a /\ Lcos lp la b

def Eq_Lcos2 (l1:Tpoint -> Tpoint -> Prop)
       (a:Tpoint -> Tpoint -> Tpoint -> Prop)
       (b:Tpoint -> Tpoint -> Tpoint -> Prop)
       (l2:Tpoint -> Tpoint -> Prop)
       (c:Tpoint -> Tpoint -> Tpoint -> Prop)
       (d:Tpoint -> Tpoint -> Tpoint -> Prop) :=
  exists lp, Lcos2 lp l1 a b /\ Lcos2 lp l2 c d

def Lcos3 lp l a b c :=
  exists la lab, Lcos la l a /\ Lcos lab la b /\ Lcos lp lab c

def Eq_Lcos3 (l1:Tpoint -> Tpoint -> Prop)
       (a:Tpoint -> Tpoint -> Tpoint -> Prop)
       (b:Tpoint -> Tpoint -> Tpoint -> Prop)
       (c:Tpoint -> Tpoint -> Tpoint -> Prop)
       (l2:Tpoint -> Tpoint -> Prop)
       (d:Tpoint -> Tpoint -> Tpoint -> Prop)
       (e:Tpoint -> Tpoint -> Tpoint -> Prop)
       (f:Tpoint -> Tpoint -> Tpoint -> Prop) :=
  exists lp, Lcos3 lp l1 a b c /\ Lcos3 lp l2 d e f

/-- Definition 14.1. -/

def Ar1 (O E A B C:Tpoint) :=
 O ≠ E /\ Col O E A /\ Col O E B /\ Col O E C

def Ar2 (O E E' A B C:Tpoint) :=
 ¬ Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C

/-- Definition 14.2. -/

def Pj (A B C D:Tpoint) := Par A B C D \/ C = D

/-- Definition 14.3. -/

def SumGeoLean (O E E' A B C:Tpoint) :=  -- was Sum
 Ar2 O E E' A B C /\
 exists A' C',
 Pj E E' A  A' /\ Col O E' A' /\
 Pj O E  A' C' /\
 Pj O E' B  C' /\
 Pj E' E C' C

def Proj P Q A B X Y :=
  A ≠ B /\ X ≠ Y /\ ¬ Par A B X Y  /\ Col A B Q /\ (Par P Q X Y \/ P = Q)

def Sump (O E E' A B C:Tpoint) :=
 Col O E A /\ Col O E B /\
 exists A' C' P',
   Proj A A' O E' E E' /\
   Par O E A' P' /\
   Proj B C' A' P' O E' /\
   Proj C' C O E E E'

/-- Definition 14.4. -/

def ProdGeoLean (O E E' A B C: Tpoint) := -- was Prod
 Ar2 O E E' A B C /\
 exists B', Pj E E' B B' /\ Col O E' B' /\ Pj E' A B' C

def Prodp (O E E' A B C:Tpoint) :=
 Col O E A /\ Col O E B /\
 exists B', Proj B B' O E' E E' /\ Proj B' C O E A E'

/-- Definition 14.8. -/

def Opp (O E E' A B:Tpoint) :=
 SumGeoLean O E E' B A O

/-- Definition 14.38. -/

def Diff (O E E' A B C:Tpoint) :=
  exists B', Opp O E E' B B' /\ SumGeoLean O E E' A B' C

def sum3 (O E E' A B C S:Tpoint) :=
  exists AB, SumGeoLean O E E' A B AB /\ SumGeoLean O E E' AB C S

def Sum4 (O E E' A B C D S: Tpoint) :=
  exists ABC, sum3 O E E' A B C ABC /\ SumGeoLean O E E' ABC D S

def sum22 (O E E' A B C D S:Tpoint) :=
  exists AB CD, SumGeoLean O E E' A B AB /\ SumGeoLean O E E' C D CD /\ SumGeoLean O E E' AB CD S

def Ar2_4 (O E E' A B C D:Tpoint) :=
  ¬ Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D

/-- Definition 14.34. -/

def Ps (O E A:Tpoint) := Out O A E

def Ng O E A := A ≠ O /\ E ≠ O /\ Bet A O E

/-- Definition 14.38. -/

def LtP (O E E' A B:Tpoint) := exists D, Diff O E E' B A D /\ Ps O E D

def LeP (O E E' A B:Tpoint) := LtP O E E' A B \/ A = B

def Length O E E' A B L :=
 O ≠ E /\ Col O E L /\ LeP O E E' O L /\ Cong O L A B

/-- Definition 15.1. -/

def Is_length (O E E' A B L:Tpoint) :=
 Length O E E' A B L \/ (O = E /\ O = L)

def Sumg (O E E' A B C:Tpoint) :=
  SumGeoLean O E E' A B C \/ (¬ Ar2 O E E' A B B /\ C = O)

def Prodg (O E E' A B C: Tpoint) :=
  ProdGeoLean O E E' A B C \/ (¬ Ar2 O E E' A B B /\ C = O)

def PythRel (O E E' A B C: Tpoint) :=
  Ar2 O E E' A B C /\
  ((O = B /\ (A = C \/ Opp O E E' A C)) \/
   exists B', Perp O B' O B /\ Cong O B' O B /\ Cong O C A B')

def SignEq (O E A B: Tpoint) := Ps O E A /\ Ps O E B \/ Ng O E A /\ Ng O E B

def LtPs (O E E' A B: Tpoint) := exists D, Ps O E D /\ SumGeoLean O E E' A D B

/-- Definition 16.1. -/
/- We skip the case of dimension 1. -/

def Cs O E S U1 U2 :=
   O ≠ E /\ Cong O E S U1 /\ Cong O E S U2 /\ Per U1 S U2


/-- Q is the orthogonal projection of P on the line AB. -/

def Projp P Q A B :=
  A ≠ B /\ ((Col A B Q /\ Perp A B P Q) \/ (Col A B P /\ P = Q))

/-- Definition 16.5. -/
/- P is of coordinates (X,Y) in the grid SU1U2 using unit length OE. -/

def Cd O E S U1 U2 P X Y :=
  Cs O E S U1 U2 /\ Coplanar P S U1 U2 /\
  (exists PX, Projp P PX S U1 /\ Cong_3 O E X S U1 PX) /\
  (exists PY, Projp P PY S U2 /\ Cong_3 O E Y S U2 PY)


/-- Strict betweenness -/

def BetS (A B C:Tpoint) : Prop := Bet A B C /\ A ≠ B /\ B ≠ C

/-- Definition of the sum of segments.
    SumS A B C D E F means that AB + CD = EF. -/

def SumS A B C D E F := exists P Q R,
  Bet P Q R /\ Cong P Q A B /\ Cong Q R C D /\ Cong P R E F

/-- PQ is the perpendicular bisector of segment AB -/

def Perp_bisect P Q A B := ReflectL A B P Q /\ A ≠ B

def Perp_bisect_bis (P Q A B:Tpoint) :=
  exists I, Perp_at I P Q A B /\ Midpoint I A B

def Is_on_perp_bisect P A B := Cong A P P B

/-- Definition of the sum of angles.
    SumA A B C D E F G H I means that ABC + DEF = GHI. -/

def SumA A B C D E F G H I :=
  exists J, CongA C B J D E F /\ ¬ OS B C A J /\ Coplanar A B C J /\ CongA A B J G H I

/-- The SAMS predicate describes the fact that the sum of the two angles is "at most straight" -/

def SAMS A B C D E F :=
  A ≠ B /\ (Out E D F \/ ¬ Bet A B C) /\
  exists J, CongA C B J D E F /\ ¬ OS B C A J /\ ¬ TS A B C J /\ Coplanar A B C J

/-- Supplementary angles -/

def SuppA A B C D E F :=
  A ≠ B /\ exists A', Bet A B A' /\ CongA D E F C B A'

/-- Definition of the sum of the interior angles of a triangle.
    TriSumA A B C D E F means that the sum of the angles of the triangle ABC
    is equal to the angle DEF -/

def TriSumA (A B C D E F:Tpoint) :=
  exists G H I, SumA A B C B C A G H I /\ SumA G H I C A B D E F

/-- The difference between a straight angle and the sum of the angles of the triangle ABC.
    It is a non-oriented angle, so we can't discriminate between positive and negative difference -/

def Defect (A B C D E F:Tpoint) := exists G H I,
  TriSumA A B C G H I /\ SuppA G H I D E F

/-- P is on the circle of center A going through B -/

def OnCircle P A B := Cong A P A B


/-- P is inside or on the circle of center A going through B -/

def InCircle P A B := Le A P A B

/-- P is outside or on the circle of center A going through B -/

def OutCircle P A B := Le A B A P

/-- P is strictly inside the circle of center A going through B -/

def InCircleS P A B := Lt A P A B

/-- P is strictly outside the circle of center A going through B -/

def OutCircleS P A B := Lt A B A P

/-- The line segment AB is a diameter of the circle of center O going through P -/

def Diam A B O P := Bet A O B /\ OnCircle A O P /\ OnCircle B O P

def EqC (A B C D:Tpoint) :=
 forall X, OnCircle X A B <-> OnCircle X C D

/-- The circles of center A passing through B and
                of center C passing through D intersect
                in two distinct points P and Q. -/

def InterCCAt A B C D P Q :=
  ¬ EqC A B C D /\
  P ≠ Q /\ OnCircle P C D /\ OnCircle Q C D /\ OnCircle P A B /\ OnCircle Q A B


/-- The circles of center A passing through B and
                of center C passing through D
                have two distinct intersections. -/

def InterCC (A B C D:Tpoint) :=
 exists P Q, InterCCAt A B C D P Q

/-- The circles of center A passing through B and
                of center C passing through D
                are tangent. -/

--def TangentCC A B C D := ∃! X:Tpoint, OnCircle X A B /\ OnCircle X C D

/- The line AB is tangent to the circle OP -/

--def Tangent (A B O P:Tpoint) := exists !X, Col A B X /\ OnCircle X O P

--def TangentAt A B O P T := Tangent A B O P /\ Col A B T /\ OnCircle T O P

/- The points A, B, C and D belong to a same circle -/

def Concyclic (A B C D:Tpoint) := Coplanar A B C D /\
  exists O P, OnCircle A O P /\ OnCircle B O P /\ OnCircle C O P /\ OnCircle D O P

/-- The points A, B, C and D are concyclic or lined up -/

def Concyclic_gen (A B C D:Tpoint) :=
  Concyclic A B C D \/ (Col A B C /\ Col A B D /\ Col A C D /\ Col B C D)

/-- C is on the graduation based on [AB] -/
inductive Grad : Tpoint -> Tpoint -> Tpoint -> Prop where
  | grad_init : forall A B, Grad A B B
  | grad_stab : forall A B C C',
                  Grad A B C ->
                  Bet A C C' -> Cong A B C C' ->
                  Grad A B C'

def Reach A B C D := exists B', Grad A B B' /\ Le C D A B'

/-- There exists n such that AC = n times AB and DF = n times DE -/
inductive Grad2 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                  Prop where
  | grad2_init : forall A B D E, Grad2 A B B D E E
  | grad2_stab : forall A B C C' D E F F',
                   Grad2 A B C D E F ->
                   Bet A C C' -> Cong A B C C' ->
                   Bet D F F' -> Cong D E F F' ->
                   Grad2 A B C' D E F'

/-- Graduation based on the powers of 2 -/
inductive GradExp : Tpoint -> Tpoint -> Tpoint -> Prop where
  | gradexp_init : forall A B, GradExp A B B
  | gradexp_stab : forall A B C C',
                     GradExp A B C ->
                     Bet A C C' -> Cong A C C C' ->
                     GradExp A B C'

inductive GradExp2 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                     Prop where
  | gradexp2_init : forall A B D E, GradExp2 A B B D E E
  | gradexp2_stab : forall A B C C' D E F F',
                      GradExp2 A B C D E F ->
                      Bet A C C' -> Cong A C C C' ->
                      Bet D F F' -> Cong D F F F' ->
                      GradExp2 A B C' D E F'

/-- There exists n such that the angle DEF is congruent to n times the angle ABC -/
inductive GradA : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                  Prop where
  | grada_init : forall A B C D E F, CongA A B C D E F -> GradA A B C D E F
  | grada_stab : forall A B C D E F G H I,
                   GradA A B C D E F ->
                   SAMS D E F A B C -> SumA D E F A B C G H I ->
                   GradA A B C G H I

/-- There exists n such that the angle DEF is congruent to 2^n times the angle ABC -/
inductive GradAExp : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                     Prop where
  | gradaexp_init : forall A B C D E F, CongA A B C D E F -> GradAExp A B C D E F
  | gradaexp_stab : forall A B C D E F G H I,
                      GradAExp A B C D E F ->
                      SAMS D E F D E F -> SumA D E F D E F G H I ->
                      GradAExp A B C G H I

/-- Parallelogram -/

def Parallelogram_strict A B A' B' :=
  TS A A' B B' /\ Par A B A' B' /\ Cong A B A' B'

def Parallelogram_flat A B A' B' :=
  Col A B A' /\ Col A B B' /\
  Cong A B A' B' /\ Cong A B' A' B /\
  (A ≠ A' \/ B ≠ B')

def Parallelogram (A B A' B':Tpoint) :=
  Parallelogram_strict A B A' B' \/ Parallelogram_flat A B A' B'

def Plg (A B C D:Tpoint) :=
  (A ≠ C \/ B ≠ D) /\ exists M, Midpoint M A C /\ Midpoint M B D

/-- Rhombus -/

def Rhombus A B C D := Plg A B C D /\ Cong A B B C

/-- Rectangle -/

def Rectangle A B C D := Plg A B C D /\ Cong A C B D

/-- Square -/

def Square A B C D := Rectangle A B C D /\ Cong A B B C

/-- Kite -/

def Kite A B C D := Cong B C C D /\ Cong D A A B

/-- Saccheri -/

def Saccheri A B C D :=
  Per B A D /\ Per A D C /\ Cong A B C D /\ OS A D B C

/-- Lambert -/

def Lambert (A B C D:Tpoint) :=
  A ≠ B /\ B ≠ C /\ C ≠ D /\ A ≠ D /\ Per B A D /\ Per A D C /\ Per A B C /\ Coplanar A B C D

/-- Vector -/

def EqV (A B C D:Tpoint) := Parallelogram A B D C \/ A = B /\ C = D

def SumV A B C D E F := forall D', EqV C D B D' -> EqV A D' E F

def SumV_exists A B C D E F := exists D', EqV B D' C D /\ EqV A D' E F

def Same_dir A B C D :=
  A = B /\ C = D \/ exists D', Out C D D' /\ EqV A B C D'

def Opp_dir (A B C D:Tpoint) := Same_dir A B D C

/-- Projections -/

def CongA_3 (A B C A' B' C':Tpoint) :=
  CongA A B C A' B' C' /\ CongA B C A B' C' A' /\ CongA C A B C' A' B'

end Definitions
