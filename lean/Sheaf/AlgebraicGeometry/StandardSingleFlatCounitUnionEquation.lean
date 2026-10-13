module
public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Naturality of the Mayer--Vietoris cone supplies the remaining pullback and
counit data for a bounded flat union complex (Stacks, Tag 0DJ9).
(blueprint: new-pc-standard-single-flat-counit-union-equation).

Proof: Restrict N to U, V and their intersection. Open restriction preserves
quasi-coherence and relative flatness, so the three hypotheses supply flat
presentations of these restrictions. Their bounded-above flat complexes are
K-flat. The universal derived-pullback counit is therefore invertible on each;
its identification with the pinned counit follows from uniqueness of the
left-derived functor. The presentation equations imply that the three canonical
base-change comparisons are isomorphisms. Relative Mayer--Vietoris for the
cover of U union V, and for its inverse-image cover, gives a morphism of
triangles: the squares commute by naturality of the adjunction comparisons,
including the boundary square. To obtain that square without compactness
assumptions, represent the two direct images by K-injective complexes with
injective terms. The sectionwise open counit square commutes before derivation;
its degreewise restriction-difference version is a map of short exact
Mayer--Vietoris complexes. Naturality of the short-exact-sequence boundary,
followed by the adjunction Hom equivalence and its shift compatibility,
identifies the boundary composites. No quasi-coherent direct-image refinement
of Mayer--Vietoris is required. The second and third components are the above
isomorphisms, so the first, namely the canonical comparison for N, is an
isomorphism by the two-out-of-three theorem for distinguished triangles.
The supplied K is itself bounded above and flat, so its pinned counit is also
invertible. Let a be the composite of the derived pullback of e.hom with this
counit. Define t to be the isomorphism with hom a inverse followed by the
canonical comparison. Then a followed by t.hom is the canonical comparison,
by cancellation of a with its inverse. This proves exactly the displayed
equation for the supplied K and e, without selecting a different complex. -/
theorem standardSingleFlatCounitUnionEquation
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver ((U ⊔ V).ι ≫ p))
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    letI := HasDerivedCategory.standard A.Modules
    letI := HasDerivedCategory.standard B.Modules
    ∀ (K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i))
    (e : (schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N) ≅
          DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)),
    ∃ t : DerivedCategory.Qh.obj
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≅
      (schemeDerivedDirectImage (pullback.snd ((U ⊔ V).ι ≫ p) g)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.Modules.tensorPullbackObj (pullback.fst ((U ⊔ V).ι ≫ p) g) N)),
      standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g =
        (derivedPullback g).map e.hom ≫
          (SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫ t.hom := by
  sorry
end AlgebraicGeometry
