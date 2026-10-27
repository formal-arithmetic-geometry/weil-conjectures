# GlobalVerdierDuality coefficient-universe elaboration repair

## Reason

Restore the quarantined module required by the current rework row. The recorded
2026-10-25 global-build error reaches the heartbeat limit while elaborating
Package.rationalization at line 174, then miselaborates the applications of Package
and Assertion at lines 218 and 256. Make both coefficient universes explicit at the category, operation, system and
field-scalar applications, matching Scheme.{u}, Stage.{u} and Ω : Type u. Enable
backward.isDefEq.respectTransparency and its types variant only while elaborating
Package. The original global false settings otherwise force unnecessary unfolding
while checking the large dependent coefficient-comparison equations. No reduction
rule or mathematical field is changed. The restored module retains the existing
mathematics and its single theorem hole; this delivery repairs elaboration, rather
than claiming a proof of global duality.

The archived module compiles against the currently published dependencies. The
repair makes its intended universe specialization explicit, consistently with
the already landed VerdierExchange restoration. A compile with only the first
universe annotations still timed out in Package.rationalScalar at its equality
with the canonical field comparison. With the final explicit two-universe
applications and local transparency settings, lcompile.py compiled the module
without errors or warnings in 32.8 seconds. No heartbeat or wall-time limit is
raised. The quarantine archive itself is untouched.

## Old

The complete archived module is quarantine/Sheaf/Paper/GlobalVerdierDuality.lean.
The restoration diff below records every change, including the local elaborator
settings. The original module-level settings remain unchanged.

## New

```diff
--- quarantine archive
+++ restored sandbox
@@ -55,7 +55,7 @@
 operation makes the point dual literally internal Hom into the coefficient unit.
 Source: blueprint global-duality proof step 3, identity normalization
 (blueprint: sk-thm-sf-global-duality). -/
-def identityOperation (T : Scheme.{u}) (s : Stage.{u} l) : Operation l Ω T T s where
+def identityOperation (T : Scheme.{u}) (s : Stage.{u} l) : Operation.{u, u} l Ω T T s where
   F := 𝟭 _
   G := 𝟭 _
   adjunction := Adjunction.id
@@ -66,13 +66,13 @@
 
 section Stage
 variable {X S : Scheme.{u}} {s : Stage.{u} l}
-  {F : Operation l Ω X S s} {unit : C l Ω S s}
+  {F : Operation.{u, u} l Ω X S s} {unit : C.{u, u} l Ω S s}
 
 /-- The stage data specialized to the identity of the point and the same structure
 morphism on both sides. This is the existing StageData, without a new duality notion.
 Source: blueprint global-duality proof steps 2--3
 (blueprint: sk-thm-sf-global-duality). -/
-abbrev Data (F : Operation l Ω X S s) (unit : C l Ω S s) :=
+abbrev Data (F : Operation.{u, u} l Ω X S s) (unit : C.{u, u} l Ω S s) :=
   StageData l Ω s F (identityOperation l Ω S s) F unit
 
 /-- Evaluation identifies Hom from the tensor unit to omega with omega. This is the
@@ -118,8 +118,10 @@
   [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
   [LocallyOfFiniteType (S ↘ Spec (.of D.k))] [QuasiCompact (S ↘ Spec (.of D.k))]
   [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
-  (A : System l Ω D hl (f := f)) (c : Compactification f)
-
+  (A : System.{u, u} l Ω D hl (f := f)) (c : Compactification f)
+
+set_option backward.isDefEq.respectTransparency true in
+set_option backward.isDefEq.respectTransparency.types true in
 /-- A global-duality package uses the existing exact finite-Tor categories and the
 published compact-support system. Ring realizations fix internal Hom, evaluation,
 ordinary direct image, projection and signed shifts on the actual small sites.
@@ -129,7 +131,7 @@
 Source: blueprint global-duality statement and proof steps 1--6
 (blueprint: sk-thm-sf-global-duality). -/
 structure Package where
-  unit (s : Stage.{u} l) : C l Ω S s
+  unit (s : Stage.{u} l) : C.{u, u} l Ω S s
   stage (s : Stage.{u} l) : Data l Ω (A.ring.operation c s) (unit s)
   conclusion (s : Stage.{u} l) : Conclusion l Ω (stage s)
   ring (s : RingStage.{u} l) : RingRealization l Ω f s (stage (s.stage l))
@@ -140,13 +142,13 @@
   unitX (s : RingStage.{u} l) :
     (s.inclusion l Ω X).obj (stage (s.stage l)).closedX.monoidal.tensorUnit ≅ ringUnit l X s
   unitY (s : Stage.{u} l) : (stage s).closedY.monoidal.tensorUnit ≅ unit s
-  unitX_normalized (s : RingStage.{u} l) (K : C l Ω X (s.stage l)) :
+  unitX_normalized (s : RingStage.{u} l) (K : C.{u, u} l Ω X (s.stage l)) :
     (s.inclusion l Ω X).map ((stage (s.stage l)).closedX.monoidal.rightUnitor K).hom =
       (ring s).tensorX.hom.app (K, (stage (s.stage l)).closedX.monoidal.tensorUnit) ≫
         (ring s).modelX.closed.tensor.map (Prod.mkHom (𝟙 _)
           ((unitX s).hom ≫ (ring s).modelX.unitIso.inv)) ≫
         ((ring s).modelX.closed.monoidal.rightUnitor ((s.inclusion l Ω X).obj K)).hom
-  unitY_normalized (s : RingStage.{u} l) (K : C l Ω S (s.stage l)) :
+  unitY_normalized (s : RingStage.{u} l) (K : C.{u, u} l Ω S (s.stage l)) :
     (s.inclusion l Ω S).map ((stage (s.stage l)).closedY.monoidal.rightUnitor K).hom =
       (ring s).tensorY.hom.app (K, (stage (s.stage l)).closedY.monoidal.tensorUnit) ≫
         (ring s).modelY.closed.tensor.map (Prod.mkHom (𝟙 _)
@@ -167,27 +169,28 @@
           (pbcDerivedExtend (a.map S)).map (ring s).unitIso.hom ≫ ringUnitScalar l a S
   rationalization (E : FieldStage.{u} l) :
     ∃ b : StageScalar l Ω (stage (.integral E)) (stage (.rational E))
-        (ConstructibleExceptionalCoefficients.rationalization l Ω E X)
-        (ConstructibleExceptionalCoefficients.rationalization l Ω E S)
-        (ConstructibleExceptionalCoefficients.rationalization l Ω E S),
+        (ConstructibleExceptionalCoefficients.rationalization.{u, u} l Ω E X)
+        (ConstructibleExceptionalCoefficients.rationalization.{u, u} l Ω E S)
+        (ConstructibleExceptionalCoefficients.rationalization.{u, u} l Ω E S),
       ScalarConclusion l Ω b ∧
       Nonempty (ScalarShifts l Ω (conclusion (.integral E)).exchange
         (conclusion (.rational E)).exchange b) ∧
       b.exceptional = A.fields.rationalizationComparison c E
   rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
     ∃ b : StageScalar l Ω (stage (.rational E)) (stage (.rational L))
-        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i X)
-        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i S)
-        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i S),
+        (ConstructibleExceptionalCoefficients.rationalScalar.{u, u} l Ω E L i X)
+        (ConstructibleExceptionalCoefficients.rationalScalar.{u, u} l Ω E L i S)
+        (ConstructibleExceptionalCoefficients.rationalScalar.{u, u} l Ω E L i S),
       ScalarConclusion l Ω b ∧
       Nonempty (ScalarShifts l Ω (conclusion (.rational E)).exchange
         (conclusion (.rational L)).exchange b) ∧
       b.exceptional = A.fields.rationalComparison c E L i
   common (i : AlgebraicallyClosedCoefficients.Index l Ω) :
-    ∃ b : StageScalar l Ω (stage (.rational (commonField l Ω i))) (stage .closed)
-        (commonInclusion l Ω X i) (commonInclusion l Ω S i) (commonInclusion l Ω S i),
-      ScalarConclusion l Ω b ∧
-      Nonempty (ScalarShifts l Ω (conclusion (.rational (commonField l Ω i))).exchange
+    ∃ b : StageScalar l Ω (stage (.rational (commonField.{u, u} l Ω i))) (stage .closed)
+        (commonInclusion.{u, u} l Ω X i) (commonInclusion.{u, u} l Ω S i)
+        (commonInclusion.{u, u} l Ω S i),
+      ScalarConclusion l Ω b ∧
+      Nonempty (ScalarShifts l Ω (conclusion (.rational (commonField.{u, u} l Ω i))).exchange
         (conclusion .closed).exchange b) ∧
       b.exceptional = A.common.commonComparison c i
 
@@ -213,7 +216,7 @@
     [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
     [IsSeparated (X ↘ Spec (.of D.k))] : Prop :=
   letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
-  ∀ (A : System l Ω D hl (f := X ↘ Spec (.of D.k)))
+  ∀ (A : System.{u, u} l Ω D hl (f := X ↘ Spec (.of D.k)))
     (c : Compactification (X ↘ Spec (.of D.k))),
     Nonempty (Package l Ω D hl (X ↘ Spec (.of D.k)) A c)
 
```

Both universes specialize to u, as required by the surrounding schemes, stages
and coefficient closure. Package locally uses transparency-respecting unification;
the scope ends with that structure. No declaration is made irreducible, no equation
changes, and no data witness is replaced. All declaration names, binder order,
fields and public imports are preserved. The public theorem signature and proof
are verbatim unchanged from the archive.

## Users

The live downstream scans with --allow-missing, for Package and Assertion, each
report zero modules because this item is quarantined. A separate textual scan of
lean/ and quarantine/ finds no importer or consumer of this Sheaf module; the
source-library GlobalVerdierDuality module is a different module and is untouched.
Both DAG attachments, sk-thm-sf-global-duality and thm-sf-global-duality, remain
attached to this restored module and declaration. Its unit route and all planned
proof dependencies remain in place. No absence of importers is used to withdraw
any module or dependency.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.GlobalVerdierDuality | G5 | Restore archive and specify coefficient universes. |

## Status

landed 20261025T043237-L-1691938 2026-10-25 (merge of deliver/G5/Sheaf.Paper.GlobalVerdierDuality)
