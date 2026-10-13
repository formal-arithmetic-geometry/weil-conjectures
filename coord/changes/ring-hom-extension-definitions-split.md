# CategoryTheory ring Hom extension shared definitions

## Reason

Separate the six existing shared definitions from the existence theorem so that the
new degree-map and differential-compatibility modules can use them without an import
cycle. The item publicly re-exports the new definitions module. All six names,
signatures, bodies, universes, visibility and docstrings are retained verbatim.
No target statement or mathematical meaning changes. The new definitions module enables
`backward.isDefEq.respectTransparency` to avoid eager unfolding of the chosen Hom-complex
witness during elaboration; the declaration text remains verbatim. The pure-tensor
definition retains the original setting locally so that constant-sheaf module
instances can be inferred. No existing downstream source
requires adaptation: it still sees exactly the same constants through the item.

## Old

The following declarations were in Sheaf.Algebra.Homology.NormalizedRingHomExtension:

```lean
/-- Modules on the one-object bottom-topology site with ring `A`. Source: Stacks,
more-algebra.tex, equation-base-change-RHom
(blueprint: def-pc-perfect-rhom-base-change-map). -/
abbrev RingSiteModules (A : Type u) [CommRing A] :=
  SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A))

/-- The map of constant ring sheaves induced by the given ring homomorphism. Source:
Stacks, equation-base-change-RHom (blueprint: def-pc-perfect-rhom-base-change-map). -/
def ringSiteMap {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    CochainComplex.onePointRingSheaf A ⟶ CochainComplex.onePointRingSheaf B :=
  ⟨(Functor.const _).map (CommRingCat.ofHom φ)⟩

/-- The projections of the shared Hom complex, taken from exactly the witness used in
`homComplexFunctor`, rather than from another product. Source: Stacks, sites-cohomology.tex,
0A8X (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringHomComplexProjection {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n p : ℤ) :
    (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n ⟶
      SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
        (P.X p) (Q.X (p + n)) :=
  (homComplex_exists (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose
    P Q n p (p + n) rfl

/-- Evaluate a product coordinate of the shared Hom complex on the unique object's slice.
Source: Stacks, 0A8X (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringHomEvaluate {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n p : ℤ)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
    (x : (P.X p).val.obj U) : (Q.X (p + n)).val.obj U :=
  (((ringHomComplexProjection P Q n p).val.app U f).app (op (Over.mk (𝟙 U.unop)))) x

/-- Termwise extension on complexes using the specified additive structure. Source:
Stacks, 06YY (blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringExtensionComplex {A B : Type u} [CommRing A] [CommRing B]
    (F : RingSiteModules A ⥤ RingSiteModules B) (hF : F.Additive) :
    CochainComplex (RingSiteModules A) ℤ ⥤ CochainComplex (RingSiteModules B) ℤ := by
  letI := hF
  exact F.mapHomologicalComplex (.up ℤ)

/-- The pure tensor, followed by the shared sheafification unit and the specified object
identification for extension. Source: Stacks, 03EK
(blueprint: def-pc-perfect-rhom-base-change-map). -/
noncomputable def ringExtensionPure {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b : B) (x : M.val.obj U) :
    (F.obj M).val.obj U :=
  (eqToHom (h M).symm).val.app U
    ((toSheafify ⊥
      (SheafOfModules.changeOfRingsPresheaf (ringSiteMap φ) M).presheaf).app U
        (b ⊗ₜ[A, φ] x))

```

## New

The exact declarations above live in Sheaf.Algebra.Homology.RingHomExtensionDefs.
The original module has:

```lean
public import Sheaf.Algebra.Homology.RingHomExtensionDefs
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.NormalizedRingHomExtension | Q3 | Re-exports all six constants unchanged. |
| Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap | unclaimed | Unchanged names, types, bodies and visibility through the public import. |
| Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree | unclaimed | Same shared projection, evaluation, extension and pure tensors. |
| Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension | unclaimed | Same scalar-extension constants. |
| Sheaf.Algebra.Homology.RingHomExtensionTransport | unclaimed | Same scalar-extension constants. |
| Sheaf.Algebra.Homology.RingExtensionFiniteSupportProduct | unclaimed | Same scalar-extension constants. |
| Sheaf.Algebra.Homology.RingExtensionInternalHomExt | unclaimed | Same scalar-extension constants. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees | Q2 | Same Hom evaluation constant. |
| Sheaf.Algebra.Homology.PerfectRingHomScalarExtension | unclaimed | Unchanged transitive public interface. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential | S1 | Same Hom projection and extension-complex constants. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso | unclaimed | Unchanged transitive public interface. |
| Sheaf.Algebra.Homology.PerfectRingDualTermFlat | unclaimed | Same Hom projection. |
| Sheaf.Algebra.Homology.PerfectRingHomKFlat | unclaimed | Unchanged transitive public interface. |
| Sheaf.Algebra.Homology.BaseChangeRHomPerfect | unclaimed | Unchanged transitive public interface. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition | unclaimed | Same shared constants through the public re-export; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeIsIso | unclaimed | Same shared constants through the public re-export; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeMap | unclaimed | Same shared constants through the public re-export; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorPostcomposition | S1 | Same ring-site module category and Hom projection through the public re-export; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorPrecomposition | S1 | Same ring-site module category and Hom projection through the public re-export; no adaptation. |

## Status

landed 20261013T151135-L-877768 2026-10-13 (merge of deliver/Q3/Sheaf.Algebra.Homology.NormalizedRingHomExtension)
