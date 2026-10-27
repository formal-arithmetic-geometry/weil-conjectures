# AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor canonical aliases

## Reason

Reuse the existing scalar comparison category, restriction and standard derived localization,
and the existing clopen native monoidal and symmetry interfaces.
The scalar and tensor interfaces reduce to the same original constructions. Category and
restriction aliases use the tensor interface; native localization, monoidal and symmetry
data use the clopen monoidal interface. The existing derived proof uses an explicit
coordinate equivalence instance to preserve its original typeclass inference. These aliases denote the same constructions, with the same coefficient and morphism
universes. Keeping one spelling avoids repeated elaboration of the site pushforward inside
dependent quotient and compositor equations. The public import of
`Sheaf.AlgebraicGeometry.ProEtaleClopenMonoidalNormalization` supplies these public bodies.
The scalar-data API is a private proof import; it is not exposed by the item.
Profiling showed 33 seconds of kernel checking at the tensor assembly, comparing two
wrappers of the same large native structure. Sharing the clopen interface avoids this
definitional diamond while keeping the native tensor and all constraints identical.
No theorem signature, tensor structure, coefficient action or restriction map changes.
The `hasDerived` instance is marked `@[instance_reducible]`; its value remains the standard
localization. Independent target-definition review applies in the normal way.

## Old

```lean
abbrev Modules {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ringedSiteModules.{max u (t + 1)}
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)

abbrev rings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (topology Y) (topology X)

abbrev restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Modules.{t, u} R ⥤ Modules.{t, u} ((rings.{t, u} j).obj R) :=
  clopenModuleRestriction j
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj R)

instance hasDerived {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    HasDerivedCategory.{max (u + 1) (t + 2)} (Modules.{t, u} R) :=
  HasDerivedCategory.standard (Modules.{t, u} R)

abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  (restriction.{t, u} j R).mapDerivedCategory
```

The following two existing native structure bodies also become canonical aliases:

```lean
instance derivedMonoidal {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    MonoidalCategory (DerivedCategory (Modules.{t, u} R)) :=
  RingedDerivedNative.monoidal.{t + 1, t, u} (topology X) R

instance derivedSymmetric {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    SymmetricCategory (DerivedCategory (Modules.{t, u} R)) :=
  RingedDerivedNative.symmetric.{t + 1, t, u} (topology X) R
```

## New

```lean
abbrev Modules {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  clopenTensorModules.{t, u} R

abbrev rings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  clopenTensorRings.{t, u} j

abbrev restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Modules.{t, u} R ⥤ Modules.{t, u} ((rings.{t, u} j).obj R) :=
  clopenTensorRestriction.{t, u} j R

@[instance_reducible]
instance hasDerived {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    HasDerivedCategory.{max (u + 1) (t + 2)} (Modules.{t, u} R) :=
  ClopenMonoidalDescent.hasDerived.{t, u} R

abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  ClopenMonoidalDescent.derivedRestriction.{t, u} j R
```

The two native structures now use the identical existing clopen interface:

```lean
instance derivedMonoidal {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    MonoidalCategory (DerivedCategory (Modules.{t, u} R)) :=
  ClopenMonoidalDescent.monoidal.{t, u} R

instance derivedSymmetric {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    SymmetricCategory (DerivedCategory (Modules.{t, u} R)) :=
  ClopenMonoidalDescent.symmetric.{t, u} R
```

The pure-tensor and inverse-tensorator definitions also share those canonical interfaces.
Their old values are definitionally equal to the aliases (the earlier complete assembly
already typechecked these conversions, but exceeded the wall-clock limit). Sharing them
avoids expanding the sheafification and native tensor constructions at every occurrence.

Old:

```lean
def pure {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (F H : Modules.{t, u} R) (U : X.ProEtᵒᵖ) (x : F.val.obj U) (y : H.val.obj U) :
    (F ⊗ H).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj R).obj)).unit.app (F.val ⊗ H.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := R) F H).inv.val).app U)
    (x ⊗ₜ[R.obj.obj U] y)
```

New:

```lean
def pure {X : Scheme.{t}} (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (F H : Modules.{t, u} R) (U : X.ProEtᵒᵖ) (x : F.val.obj U) (y : H.val.obj U) :
    (F ⊗ H).val.obj U :=
  clopenTensorPure.{t, u} R F H U x y
```

Old:

```lean
def tensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (restriction.{t, u} j R).Braided) (F H : Modules.{t, u} R) :
    (restriction.{t, u} j R).obj (F ⊗ H) ≅
      (restriction.{t, u} j R).obj F ⊗ (restriction.{t, u} j R).obj H :=
  letI := h
  (Functor.Monoidal.μIso (restriction.{t, u} j R) F H).symm
```

New:

```lean
def tensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (restriction.{t, u} j R).Braided) (F H : Modules.{t, u} R) :
    (restriction.{t, u} j R).obj (F ⊗ H) ≅
      (restriction.{t, u} j R).obj F ⊗ (restriction.{t, u} j R).obj H :=
  clopenTensorComparison.{t, u} j R h F H
```

Old:

```lean
def derivedTensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (derivedRestriction.{t, u} j R).Braided)
    (K L : DerivedCategory (Modules.{t, u} R)) :
    (derivedRestriction.{t, u} j R).obj (K ⊗ L) ≅
      (derivedRestriction.{t, u} j R).obj K ⊗ (derivedRestriction.{t, u} j R).obj L := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      exact (@Functor.Monoidal.μIso _ _ (derivedMonoidal.{t, u} R) _ _
        (derivedMonoidal.{t, u} ((rings.{t, u} j).obj R))
        (derivedRestriction.{t, u} j R) h.toMonoidal K L).symm
```

New:

```lean
def derivedTensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (derivedRestriction.{t, u} j R).Braided)
    (K L : DerivedCategory (Modules.{t, u} R)) :
    (derivedRestriction.{t, u} j R).obj (K ⊗ L) ≅
      (derivedRestriction.{t, u} j R).obj K ⊗ (derivedRestriction.{t, u} j R).obj L :=
  (ClopenMonoidalDescent.braidedComparison.{t, u} j R h).app (K, L)
```

The existing generic coordinate-bicone and derived-product localization proofs are moved
to two new proved modules. Their private theorem signatures in the item remain unchanged
as wrapper proofs. The private `piPreadditive`, `moduleGluing` and `derivedPi_isEquivalence`
interfaces used by `import all` consumers remain present. Unused internal coordinate and
tuple implementation declarations move with their proofs. No public theorem disappears.

The original private pointwise preadditive instance also becomes an alias of the new
public pointwise construction needed by the extracted theorem's additive hypothesis.
Its signature and data remain the same.

Old:

```lean
private local instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) where
  homGroup M N := inferInstanceAs (AddCommGroup (∀ i, M i ⟶ N i))
  add_comp _ _ _ f g h := funext (fun i ↦ Preadditive.add_comp _ _ _ (f i) (g i) (h i))
  comp_add _ _ _ f g h := funext (fun i ↦ Preadditive.comp_add _ _ _ (f i) (g i) (h i))
```

New:

```lean
private local instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) :=
  CategoryTheory.FiniteProductCoordinates.piPreadditive D
```

The already proved `finite_clopen_derived_calculus` and its canonical definitions now live
in `Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenDerivedCalculus`, publicly imported by the
item. All old public names and signatures are preserved. The module-gluing proof is exposed
there as `moduleGluingCore`; the item's original private `moduleGluing` remains a wrapper
with its exact old signature. The same holds for its private coordinate and derived-product
helpers. This extraction separates the existing derived theorem from the two assigned
proofs, after profiling and canonicalizing their large definitions.

The imported `ClopenMonoidalDescent` instances `modulesAbelian`, `hasDerived`, `monoidal`,
`symmetric`, `restrictionLimits` and `restrictionColimits` are disabled in the item and
extracted derived module. Their canonical `FiniteClopenTensor` wrappers provide the same
instances. This avoids exposing competing instance candidates to direct consumers through
the added public normalization import. Before this adjustment, the unchanged strict-tower
consumer typechecked but took 62 s, just over the 60 s file limit. No instance declaration
body or signature in the dependency module is modified.

The unchanged `Sheaf.Paper.FiniteClopenConstructibilityBounds` failed against this delivery
at its native tensor model with the original compiler error:

```text
FiniteClopenConstructibilityBounds.lean:220:85: error: stuck at solving universe constraint
  u + 1 =?= max (u + 1) ?u.11
while trying to unify ... HasDerivedCategory ... (ProEt.clopenTensorModules ...)
```

The same unresolved generic `HasDerivedCategory` and `Abelian` candidates recurred in its
native model and final bound proof (original lines 229, 234 and 391). It already excludes
the item's `hasDerived` so that the published fixed-coefficient instances are selected.
The forced adaptation adds the corresponding exclusions for the newly visible
`ClopenMonoidalDescent` and `ClopenLocalization` generic candidates, and
`ClopenScalar.derived` exposed by its existing `import all`. The smaller public interface
leaves the unchanged strict-tower consumer at 52.3 s (result
`23005eaeeff5f1aa1a223013`).
Only this new attribute block and its explanatory comment are added, before `universe u w`;
all existing signatures, visibility, proofs and attributes are retained. The module is
unclaimed at the time of this adaptation. It is compiled against the change in the same
packet. The scalar-data module is needed only by the extracted exactness proof, so its import
is private. The item has no direct public scalar-data import. Its statements and scalar
definitions continue to use the original successive-derived-quotient public API. The
strict-tower consumer retains every original public statement. Its support section is
split as described below after later fresh checks still exceed the file limit. Its four
direct consumers are checked too. No profiling or serial-elaboration option change is
delivered.

The unclaimed `Sheaf.Paper.SfClopenPreservesCompleteness` fails at original lines
73, 93, 163, 167, 430 and 440 with unresolved abelian-instance universes. The first is:

```text
max (t + 2) (u + 1) =?= max (max (max (t + 2) u) (?u.103 + 1)) (?u.104 + 1)
while trying to unify Abelian (SheafOfModules R) with
Abelian (ProEt.ClopenLocalization.Modules ... R)
```

Result `3e3f3b93ea8e216d28783622` checks the unchanged original against the new imports.
The forced adaptation adds only this line after its existing sheafification exclusion:

```lean
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
```

All original imports, declaration signatures, visibility and attributes remain identical.
After the abelian-instance exclusion, result `11aa717d84bf4e98378334c4` reaches the final
identity proof but times out finding `Mono (DerivedCategory.Q.map (𝟙 (Ψ.obj P)))`.
Only the proof of its local `hid` is simplified:

Old:

```lean
      apply (cancel_mono (DerivedCategory.Q.map (𝟙 (Ψ.obj P)))).mp
      erw [IsIso.inv_hom_id, Category.id_comp, DerivedCategory.Q.map_id]
```

New:

```lean
      apply IsIso.inv_eq_of_hom_inv_id
      erw [Category.comp_id, DerivedCategory.Q.map_id]
```

This is exactly the same inverse-of-identity equation, avoiding an unnecessary typeclass
search; no heartbeat limit is raised. Its one direct importer, `Sheaf.Paper.SfClopenDerivedCompatibility`,
is checked too; its unchanged compatibility copy is removed before submission.

The unclaimed strict-tower consumer is rejected at 67 s in
`2fb8e3f5de06b021a9f9fc72`, after the item and its definitions have been profiled and
simplified. Its original support section is moved to the new module
`Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosCore`. The first fifteen public declarations
(`Modules` through `localization`, including `restriction_exact`) retain their exact
names, signatures and definition bodies. The original module publicly imports this core
and retains all six original tower/derived declarations and proofs. The core has no
proof import of the item: only the original module's later derived-equivalence proof
needs its polymorphic helper. The generic sheafification proof import in the core is
explicit. The original node's statement and statement dependencies stay unchanged;
only the proof description, proof dependencies and Lean attachments record the split.

Eighteen private wrapper signatures in the original module are copied verbatim from the
old support section. Their proofs apply the existing proofs with a private `Core` suffix.
The private data wrappers change only by naming the original extracted construction:

Old:

```lean
private def comparison_iso [PreservesLimitsOfShape (Discrete ℕ) F] :
    roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ roosTowerAction F ⋙ roosF := by
  have (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso (roosAdditiveComparison F C) :=
    roosAdditiveComparison_isIso F C
  exact NatIso.ofComponents (fun C ↦ asIso (roosAdditiveComparison F C))
    (fun f ↦ roosAdditiveComparison_natural F f)
```

New:

```lean
private def comparison_iso [PreservesLimitsOfShape (Discrete ℕ) F] :
    roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ roosTowerAction F ⋙ roosF := by
  exact comparison_isoCore F
```

Old:

```lean
private def productSections (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u})
    (C : Towers.{t, u, v} X R) (p : ℤ) (U : X.ProEt) :
    ((roosP C).X p).val.obj (op U) ≃+
      ∀ n : ℕ, (((C.X p).obj (op n)).val.obj (op U)) :=
  let E := HomologicalComplex.eval (Modules.{t, u, v} X R) (.up ℤ) p ⋙
    SheafOfModules.evaluation R (op U)
  (PreservesProduct.iso E (fun n : ℕ ↦ C.asFunctor.obj (op n)) ≪≫
    ModuleCat.piIsoPi (fun n : ℕ ↦ E.obj (C.asFunctor.obj (op n)))).toLinearEquiv.toAddEquiv
```

New:

```lean
private def productSections (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u})
    (C : Towers.{t, u, v} X R) (p : ℤ) (U : X.ProEt) :
    ((roosP C).X p).val.obj (op U) ≃+
      ∀ n : ℕ, (((C.X p).obj (op n)).val.obj (op U)) := by
  exact productSectionsCore X R C p U
```

Old:

```lean
private def transposeAddEquiv {J K : Type*} (P : J → K → Type*)
    [∀ i k, Add (P i k)] : (∀ i k, P i k) ≃+ ∀ k i, P i k :=
  { Equiv.piComm P with map_add' := fun _ _ ↦ rfl }
```

New:

```lean
private def transposeAddEquiv {J K : Type*} (P : J → K → Type*)
    [∀ i k, Add (P i k)] : (∀ i k, P i k) ≃+ ∀ k i, P i k := by
  exact transposeAddEquivCore P
```

All six public theorem signatures and remaining proof bodies are verbatim. Existing
restriction and abelian instances are registered locally after the imports, reproducing
their original local priority. The old local irreducibility attributes of the support
API are kept in the original module. The extracted wrapper first fails in `a9413cede4f151f9e57158ec` at lines 170,
796 and 930 with unresolved `ClopenLocalization.Modules` abelian and derived universes.
Exclude `ClopenLocalization.modulesAbelian` and `ClopenLocalization.hasDerived` in
that module, preserving its original fixed-universe choices.
Every direct importer is checked against the
split; this includes the private interfaces called by `import all` consumers. No source
module under `WeilConjectures` is edited and no postponed proof is added.

The unclaimed direct strict-tower consumer
`Sheaf.Paper.ClopenCompletedOperationTowers` exceeds 60 s unchanged at 64 s
(`144c389ca7bd9de4f63372af`) and 67 s (`dc65bae996333a9f48d07c65`). Profiling
(`749eee69d1ed245314bc82e8`) identifies 22.5 s in linting. This adaptation changes
only the following module options, before its existing `set_option autoImplicit false`:

Old:

```lean
set_option autoImplicit false
```

New:

```lean
-- Avoid scanning the large specified comparison types for unused finite instances.
-- Kernel checking and the mathematical declarations are unchanged.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option autoImplicit false
```

After removing these four added lines, the file is byte-identical to the current source.
Its existing single named hole is unchanged and no new mathematical statement is added.
There are no direct Lean importers; proof checking and all declaration bodies stay unchanged.

The unclaimed direct consumer `Sheaf.Paper.AugmentedIntegralDescent` fails unchanged
in `fcf3072910f8bd9921d87d8c` at lines 144, 176, 358 and 771. The new generic
monoidal-descent abelian instance leaves `u + 1 =?= max (u + 1) ?u.23` unresolved
for its fixed `scalarReductionSource` universe. Add only this module-local exclusion
and a comment, before the existing options:

```lean
-- Keep the fixed coefficient-universe abelian structure.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
```

The narrowed check `faca1dcf6509bcd53439f2f3` exposes the analogous localization
abelian candidate, hence both exclusions above are needed.
Every original declaration signature, body and attribute, including its one original
hole, is unchanged. Its one direct importer `Sheaf.Paper.ClopenRoosIntegralDescent`
is compiled against the adaptation.

### Roos integral descent instance selection

`Sheaf.Paper.ClopenRoosIntegralDescent` is unclaimed. Original result
`b7065e002b4fa5ea92653bcb` fails at lines 235, 246, 430 and 432 with the generic
abelian candidate leaving `u + 1 =?= max (u + 1) ?u` unresolved.
Old: the original two instance exclusions only. New: an explanatory comment and
an additional exclusion of `ClopenMonoidalDescent.modulesAbelian` and
`ClopenLocalization.modulesAbelian` before the options. Existing signatures,
proofs, definition bodies, attributes and five named holes are unchanged.
The adapted file passes in 35.0 s (`45e48afdf83a65c72ada5587`).
There are no current Lean direct importers.


### Compact-support instance selection

`Sheaf.Paper.ClopenCommonCompactSupport` is unclaimed. The unchanged source fails
in `c35afa55dbef73e0125abd77` with fixed-universe `Abelian` and
`HasDerivedCategory` ambiguity at lines 129--135 and 190--205 and related later
sites. Old: the three existing exclusions only. New: a comment and an additional
block excluding generic monoidal/localization category and sheafification
instances and `ClopenScalar.derived`, before the universe declaration, as in
constructibility bounds. No original signature, proof, data or attribute changes.
The adapted file passes in 52.5 s (`a08ec9ae9d4256036843ff53`). Its two direct
importers pass unchanged (`8d68d0e0ffcac10c3fe6b750`); their validation-only
source copies have been removed.

### Private common-stage unit proof

`Sheaf.Paper.FiniteClopenDerivedDecomposition` is unclaimed. Its unchanged source
exceeds 60 s (`749eee69d1ed245314bc82e8`). The detailed trace in
`be0caf4e00e45517807bf105` locates the expensive definitional comparison in the
object formula used by private `commonUnitCheck`.

Old: `commonUnitCheck` obtains `hM` by directly applying
`(commonStageDerivedPullback_existsUnique ...).exists.choose_spec.1 M`, then
uses `eqToIso hM` and the rational-stage inclusion isomorphism.

New: add the proved private theorem `commonStagePullback_obj` with arbitrary
prime, algebraic coefficient closure, scheme morphism and object parameters.
Its conclusion is exactly the existing chosen pullback's object formula and its
proof applies that same uniqueness specification. Mark the existing functor
`commonStageDerivedPullback` locally irreducible after the lemma, and apply this
lemma instead of unfolding the functor in `commonUnitCheck`. The remaining
isomorphism composition is unchanged. No new data or mathematical assumption is
introduced. Every current public declaration, binder, attribute and body stays
identical. The one current original hole stays unchanged; the newly published
finite restriction identification proof and its private support helpers are
preserved verbatim. The isolated prefix passes in
23.9 s (`e4b792a7fbd4bb7f681c42b8`); no diagnostic options or temporary module
are delivered. Its ordinary importers see exactly the same public interface.

The refreshed full decomposition file passes in 58.9 s
(`b498e28a31f7a7f1e81912ff`). The local reducibility setting is scoped only to
`commonUnitCheck`; all subsequent original proofs use their original settings.

### Augmented-descent linting time

The first delivery stops before pushing because the full compilation takes 70 s
on `AugmentedIntegralDescent`. Profile `c97cd3eb11983b2e5ad76022` identifies 11.3 s
linting the large final statement. Old: the two unused finite/decidable-instance
linters are enabled. New: disable only `linter.unusedDecidableInType` and
`linter.unusedFintypeInType` with an explanatory comment, as for the completed
operation-towers consumer. No declaration body, signature, original attribute,
data or kernel-checking option changes. Its one original hole is untouched.
No profiler option is delivered.

The clean augmented-descent repair passes in 59.8 s
(`b1eb0cc483f4daaf1b7aa807`), with no warnings.

### Finite-clopen decomposition support split

The private formula lemma improves the common-stage unit comparison, but the
second delivery compile still takes 74 s. Explicit unfolding of only the named
pullback definition still takes 73 s (`702cdfa64b45ce8a9a4af5be`), with only
3.7 s in linting. After improving that definition, split the self-contained
support section into `Sheaf.Paper.FiniteClopenDecompositionCore`.

Old: the first support section and all twenty-four coefficient-data declarations
live in `FiniteClopenDerivedDecomposition`. New: the same declarations, signatures,
attributes and definition bodies live in the new support module, publicly imported
by the original module. All complete support proofs move with them. The new
support module uses default transparency. The original module retains every
current decomposition statement and proof, including the newly published finite
restriction identification proof and the original single hole. It imports the
private support helpers with `import all` and reinstates the same local inference
and reducibility settings. No outside module imports all of the original module;
all eleven ordinary direct importers are checked before delivery.

The existing decomposition node changes only its proof, proof dependencies, proof
origin and Lean attachment. The twenty-four moved public declarations attach to
the new proved support node. No declaration is withdrawn or weakened, and no
source-library file changes.

The first split check (`c65a06494b635fa4e5daa527`) compiles the support module
but exposes generic scalar derived/sheafification instances in the original file.
At lines 299--363 and 881--964 the first constraint is
`u + 1 =?= max (u + 1) ?u` from `ClopenScalar.derived`, with related sheaf and
product-category universe constraints. Exclude the generic scalar derived,
scalar sheafification and localization sheafification instances, preserving the
fixed coefficient-universe structures. Remove redundant original private imports
from the facade, retaining every original public import; the private proof APIs
are now supplied by `import all FiniteClopenDecompositionCore`.

The final support/facade pair and all eleven ordinary direct importers pass in
`65d75f756021f3d643b01ae1`. All nine unchanged validation-only source copies are
removed after checking their initial hashes. No further consumer source
adaptation is needed for this split. No archive or quarantined DAG attachment
is withdrawn or changed by this validation cleanup.

The next complete delivery batch rejects augmented descent at 68 s
(`l2568baf910b7a5416d667417`). The follow-up profiler result
`fcad47c80b1c1b9bcd347660` isolates the remaining tactic, type-checking, instance
inference and linting costs. Following the preceding data improvements, extract
the complete private integral Roos proof into
`Sheaf.Paper.IntegralClopenRoosCalculus`, theorem
`WeilConjectures.PurityFiniteSetting.integralClopenRoosCalculus`.
The new support module uses default transparency. Its mathematical proof is the
existing proof without changes. The original private `integralRoosCalculus`
header remains byte-identical and its body now applies that theorem. One new
private import supplies it. No public declaration, data, signature, visibility
or original attribute changes. `ClopenRoosIntegralDescent`, the one direct
importer, is checked with the extraction. The new node is entirely proved; the
parent node changes only proof, proof dependencies and proof origin.

The private Roos helper extraction compiles, but the shortened augmented
consumer still takes 63 s in `ae5b618148363288788dba5b`. Following the preceding
canonical-definition and narrow-linter improvements, split its existing support
prefix into `Sheaf.Paper.AugmentedIntegralDescentCore`. Eight original public
names, signatures, attributes and data stay identical: finite restriction,
its exactness and three instances, finite derived restriction, the augmented
reduction comparison, and normalized integral Roos descent. The same named
augmented-comparison hole moves with its declaration; no new hole is added.
The new module uses default transparency. The facade retains the exact original
membership theorem and proof and every original public import. It publicly
imports the support module and privately imports all its helpers; its finite-bound
and finite-extrema proof imports remain direct. Its original local options and
irreducibility settings are reinstated. Only the existing parent node's proof,
proof dependencies, proof origin and Lean attachment change; the new support
node owns the eight relocated declarations. No source-library declaration changes.
The one direct importer, `ClopenRoosIntegralDescent`, is checked with this split.

The final augmented support/facade and direct importer compile without warnings
in `30f2ba22f254f954f7ce86e1`; the membership facade takes 13.7 s and the
Roos-integral consumer 46.4 s. No profiling option remains. Default transparency
is retained in both new integral support modules.

The next full delivery rejects `ClopenCompletedOperationTowers` at 65 s.
The focused profile (`feb807a6a344685964792f1f`) locates 27.7 s in linting
the final statement. That statement already locally marks `TensorComparison`,
`ScalarComparison` and the operation model definitions irreducible, while the
original file globally ignores that transparency setting during backward
elaboration. Scope `backward.isDefEq.respectTransparency true` to the final
theorem. Every declaration signature, body, attribute and the existing hole
remain byte-identical; no definition or import is changed. The clean file
passes without warnings in 47.8 s (`bdd9f4a924e45ccddcb2367e`). This does not
require another support split, and no diagnostic option is delivered.

## Users

The table is the union of `tools/downstream.py` uses searches for the ten changed names.
The script matches the final name segment and includes unrelated local names. The original
private helpers remain present for the two original `import all` consumers. The constructibility consumer requires the instance exclusions described above.
All direct consumers are compiled against this delivery before submission.
The completeness consumer requires the abelian-instance exclusion and local identity
proof simplification described above.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus | X6 | Canonical aliases of the same data; proofs use their APIs. |
| Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence | unclaimed | Forced compilation split; public data and theorem signatures unchanged, used private helper signatures retained. |
| Sheaf.Paper.FiniteClopenConstructibilityBounds | unclaimed | Forced top-level instance exclusions preserve its fixed coefficient universes; all declaration signatures and proof bodies stay identical. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Forced private formula lemma and support compilation split; original public names, signatures and data unchanged. |
| Sheaf.Paper.ClopenCompletedOperationTowers | unclaimed | Forced linting-only timing adaptation; all declarations, data, proof bodies and its existing hole are unchanged. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed | Forced generic abelian-instance exclusions; all data and declaration bodies unchanged. |
| Sheaf.Paper.IntegralReductionFiniteClopenBounds | unclaimed | Direct constructibility consumer; no source adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationData | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.BoundaryFiniteSiteData | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.CoefficientFirstCompactSupportSiteSquare | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.CompactSupportProjectionFormula | F7 | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.CompleteProjectionDescentMaps | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.CoordinateTowerNormalizationData | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | P7 | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.IntegrationCoefficientProjectionNaturality | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.QcqsCompactSupportStrictReductionGamma | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.RestrictedAffineDiagonalDncVectorCoordinates | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.SystemScalarProjectionData | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.VectorTensorProjectionComparison | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.VerdierPairingThreeTransposes | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.SixFunctors.RationalVerdierModels | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Textual name match in a different declaration or docstring; no use of the changed FiniteClopenTensor comparison. |
| Sheaf.Paper.AugmentedIntegralDescent | unclaimed | Forced instance and timing repairs; private Roos proof and public support extraction preserve every existing public name, signature, data body and hole. |
| Sheaf.Paper.ClopenCommonCompactSupport | unclaimed | Forced fixed-universe instance exclusions; all original signatures, proof bodies and data unchanged. |
| Sheaf.Paper.SfClopenPreservesCompleteness | unclaimed | Forced abelian-instance exclusion and inverse characterization for the identity; signatures unchanged. |
| Sheaf.Paper.SfClopenDerivedCompatibility | unclaimed | Direct completeness consumer, no adaptation. |

| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed | Direct decomposition consumer; unchanged validation-only copy. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Direct decomposition consumer; unchanged validation-only copy. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed | Direct decomposition consumer; unchanged validation-only copy. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Direct decomposition consumer; unchanged validation-only copy. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Direct decomposition consumer; unchanged validation-only copy. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Direct decomposition consumer; unchanged validation-only copy. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Direct decomposition consumer; unchanged validation-only copy. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Direct decomposition consumer; unchanged validation-only copy. |
| Sheaf.Paper.ClopenIntegralRestriction | unclaimed | Direct decomposition consumer; unchanged validation-only copy. |

## Status

landed 20261027T151749-L-1204492 2026-10-27 (merge of deliver/X6/Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus)
