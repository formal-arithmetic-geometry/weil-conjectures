module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Irreducible
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.QuasiExcellentNagata
public import Sheaf.RingTheory.NagataRing
public import Sheaf.RingTheory.JapaneseDomain
public import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
public import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
public import Sheaf.AlgebraicGeometry.FiniteOverProjective
public import Sheaf.AlgebraicGeometry.ProperStability
public import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
public import Sheaf.RingTheory.PurelyInseparableBaseChangeLocalRing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Projective spreading and normalization after a purely inseparable generic extension

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, proof of Theorem 3.5,
Step 5, printed pp. 163–164 (blueprint: lem-trf-projective-inseparable-spread-normalization)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- Projective spreading and normalization after a purely inseparable generic extension.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, proof of Theorem 3.5,
Step 5, printed pp. 163–164 (blueprint: lem-trf-projective-inseparable-spread-normalization).
The proof has seven steps. (1) Normalize `Y` in `K` using
`def-fin-normalization-extension`, excellence, and finite integral-closure results; this gives
`b` and its function-field identification. (2) Finite-over-projective gives projectivity over
`S`, and (3) the graph-section argument gives projectivity of `b`. (4) Purely inseparable
base change supplies a unique dominant component `W` of `X₀ ×_Y Y₁`. (5) Normalize `W`;
finite normalization and stability of properness give `X₁`, `c`, and `f`, with the displayed
composition and generic finiteness. (6) Localization of integral closures identifies the
normalization on the generic fibre with the normalization of the corresponding component.
(7) Composing with any proper dominant generically finite `a` preserves these properties.
The statements used in these steps are the proof dependencies recorded by the DAG.

The identification `κ(Y₁) ≅ K` is one of `κ(Y)`-algebras (the generic point `Spec K ⟶ Y₁ ⟶ Y`
is the given `Spec K ⟶ Spec κ(Y) ⟶ Y`); `c` and `f` are the composites of the normalization
`n`, the component `j` and the two projections of `X₀ ×_Y Y₁`; and the generic-fibre
identification is an isomorphism over `X₀` and over `Spec K ≅ Spec κ(y₁)`.
-/
theorem projective_inseparable_spread_normalization
    (A : Type u) [CommRing A]
    (hbase : IsField A ∨
      ∃ hD : IsDomain A,
        Nonempty (@IsDiscreteValuationRing A inferInstance hD) ∧ IsExcellent A)
    (S : Scheme.{u}) (eS : S = Spec (.of A))
    (Y : Scheme.{u}) (p : Y ⟶ S) [IsIntegral Y]
    (hYexc : ∀ U : Y.Opens, IsAffineOpen U → IsExcellent Γ(Y, U))
    [IsHProjective p] (hpdom : DenseRange p.base)
    (X₀ : Scheme.{u}) [IsIntegral X₀]
    (hXexc : ∀ U : X₀.Opens, IsAffineOpen U → IsExcellent Γ(X₀, U))
    (g : X₀ ⟶ Y) [IsProper g] (hgdom : DenseRange g.base)
    (K : Type u) [Field K] [Algebra Y.functionField K]
    (hKpure : IsPurelyInseparable Y.functionField K)
    (hKfin : Module.Finite Y.functionField K) :
    ∃ (Y₁ : Scheme.{u}) (hY₁ : IsIntegral Y₁) (b : Y₁ ⟶ Y),
      (∀ U : Y₁.Opens, IsAffineOpen U → IsExcellent Γ(Y₁, U)) ∧
      IsFinite b ∧ IsHProjective b ∧ IsProper b ∧ DenseRange b.base ∧
      (∃ φ : (@Scheme.functionField Y₁ (irreducibleSpace_of_isIntegral Y₁)) ≅ CommRingCat.of K,
        Spec.map φ.hom ≫ Y₁.fromSpecFunctionField ≫ b =
          Spec.map (CommRingCat.ofHom (algebraMap Y.functionField K)) ≫
            Y.fromSpecFunctionField) ∧
      IsHProjective (b ≫ p) ∧
      ∃ (W : Scheme.{u}) (hW : IsIntegral W)
        (j : W ⟶ pullback g b),
        IsClosedImmersion j ∧
        Set.range j.base ∈ irreducibleComponents ((pullback g b : Scheme.{u}) : Type u) ∧
        DenseRange (j ≫ pullback.snd g b).base ∧
        ∃ (X₁ : Scheme.{u}) (hX₁ : X₁ = @Scheme.normalization W hW)
          (n : X₁ ⟶ W),
          IsIntegral X₁ ∧
          (∀ U : X₁.Opens, IsAffineOpen U → IsExcellent Γ(X₁, U)) ∧
          n = eqToHom hX₁ ≫ @Scheme.fromNormalization W hW ∧
          IsFinite n ∧ IsProper n ∧
          ∃ (c : X₁ ⟶ X₀) (f : X₁ ⟶ Y₁),
            c = n ≫ j ≫ pullback.fst g b ∧ f = n ≫ j ≫ pullback.snd g b ∧
            IsProper c ∧ DenseRange c.base ∧
            IsProper f ∧ DenseRange f.base ∧
            c ≫ g = f ≫ b ∧
            (∃ U : X₀.Opens, Dense (U : Set X₀) ∧ IsFinite (c ∣_ U)) ∧
            (∀ {X : Scheme.{u}} (a : X₀ ⟶ X),
              IsProper a → DenseRange a.base →
              (∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (a ∣_ U)) →
              IsProper (c ≫ a) ∧ DenseRange (c ≫ a).base ∧
                (∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite ((c ≫ a) ∣_ U))) ∧
            (∀ (y₁ : Y₁), IsGenericPoint y₁ Set.univ →
              ∃ (ψ : Y₁.residueField y₁ ≅ CommRingCat.of K),
                Spec.map ψ.hom ≫ Y₁.fromSpecResidueField y₁ ≫ b =
                  Spec.map (CommRingCat.ofHom (algebraMap Y.functionField K)) ≫
                    Y.fromSpecFunctionField ∧
              ∃ (Z : Scheme.{u}) (hZ : IsIntegral Z) (jη : Z ⟶
                pullback
                  g
                  (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField K)) ≫
                    Y.fromSpecFunctionField)),
                IsClosedImmersion jη ∧
                Set.range jη.base ∈ irreducibleComponents
                  (((pullback
                    g
                    (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField K)) ≫
                      Y.fromSpecFunctionField) : Scheme.{u}) : Type u)) ∧
                ∃ e : f.fiber y₁ ≅ @Scheme.normalization Z hZ,
                  e.hom ≫ @Scheme.fromNormalization Z hZ ≫ jη ≫ pullback.fst _ _ =
                    f.fiberι y₁ ≫ c ∧
                  e.hom ≫ @Scheme.fromNormalization Z hZ ≫ jη ≫ pullback.snd _ _ =
                    f.fiberToSpecResidueField y₁ ≫ Spec.map ψ.inv) := by
  sorry

end AlgebraicGeometry

end
