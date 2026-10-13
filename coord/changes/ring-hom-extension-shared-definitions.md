# CategoryTheory ring Hom scalar-extension definitions

## Reason

The expanded normalization formula in the supporting theorem caused repeated large
conversion checks against the original named definitions and the item exceeded the
60-second compile limit. Relocate the six shared definitions to the supporting module
so that the helper statement uses precisely the same constants as the data fields.
The original module publicly imports the supporting module. Every name, signature,
body, visibility and docstring is retained verbatim. There is no changed target meaning. Second reading also minimizes imports: derived
extension and resolution theorems are needed only by proofs, while the public signature
needs the Mathlib left-derived-functor definition and Module.Finite.

## Old

The following declarations lived in Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap:

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

The original import block also included:

```lean
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Sheaf.Algebra.Homology.KFlatResolution
public import Mathlib.Algebra.Module.FinitePresentation
```

## New

The exact declarations above now live in Sheaf.Algebra.Homology.NormalizedRingHomExtension,
with identical signatures and bodies. The original module re-exports them through:

```lean
public import Sheaf.Algebra.Homology.NormalizedRingHomExtension
```

The imports above are replaced by:

```lean
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolution
public import Mathlib.RingTheory.Finiteness.Defs
```

KFlatTensorQuasiIso remains publicly available through the supporting module.
No downstream statement uses a removed finite-presentation or proof-only declaration.
All twelve unchanged downstream users are checked against the delivered outputs, including
the two tensor comparison modules named in the latest landing return.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.BaseChangeRHomPerfect | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap | T3 | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.PerfectRingHomKFlat | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.PerfectRingHomScalarExtension | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.PerfectRingDualTermFlat | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.RingExtensionFiniteSupportProduct | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.RingExtensionInternalHomExt | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |
| Sheaf.Algebra.Homology.RingHomExtensionTransport | unclaimed | Same public constants re-exported from the original module; no signature or meaning change. |

## Status

landed 20261013T111927-L-3064663 2026-10-13 (merge of deliver/T3/Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap)
