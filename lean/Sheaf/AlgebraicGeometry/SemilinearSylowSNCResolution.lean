module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.SemilinearSylowGoodComponents
import Sheaf.AlgebraicGeometry.ClopenGeometricCategoricalQuotient
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Resolution of a semilinear Sylow quotient with SNC boundary

Source: ILO, Travaux de Gabber, Expose X 2.3, Step 2, diagram (2.c), p. 151,
and Step 3, pp. 151--152 (blueprint: lem-sfb-semilinear-sylow-snc-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A Sylow quotient followed by a tame resolution preserves prime-to-ell generic degrees.
The quotients and their descent maps are supplied for each subgroup; categorical uniqueness
makes these the actual descents of `h`. The action on constants is pulled back by the inverse
field automorphism, so `a` is a left scheme action. `F` is the actual intermediate fixed field.
The clopen `U` is a union of components of `Q L`, and its inverse image is the selected source.
Residue fields are identified by bijectivity of the canonical residue-field map of `vR`.
The final stalk ideal is a product of distinct parameters. Its prime factors are precisely
the equations of the reduced boundary components through the point. The empty product is 1.

Source: ILO X 2.3, Step 2, diagram (2.c), p. 151, and Step 3, pp. 151--152
(blueprint: lem-sfb-semilinear-sylow-snc-resolution).

Proof (the six steps of the DAG):
1. Choose an ell-Sylow subgroup L. Its order is an ell-power and its index is prime to ell.
   Use lem-weil-pbc-sylow-subgroup-prime-index.
2. Apply lem-sfb-semilinear-sylow-good-components to the given model and subgroup quotients.
   It gives F = K^L, the asserted field degrees, the clopen union U and its clopen inverse
   image, projectivity over F and B, surjectivity, and the prime-to-ell residue degree at
   every retained generic point. The quotient over the dense open supplies its hypotheses.
3. Restrict smoothness, projectivity and D to the clopen source. Each integral component
   lies wholly in this source or in its complement. The retained intersections are unchanged;
   the intersection indexed by the empty set is the clopen source. Use
   lem-weil-pbc-smooth-restrict-open-subschemes, def-weil-closed-immersion,
   def-kun-projective and def-trf-smooth-strict-normal-crossings-divisor.
4. L has ell-power order, invertible in F. Restrict the categorical geometric quotient,
   its invariant sections and its descended F-structure. D remains invariant since h is
   invariant. Use lem-sfb-clopen-geometric-categorical-quotient and
   lem-sfb-semilinear-quotient-projective-geometry.
5. Apply lem-sfb-tame-snc-quotient-resolution to the restricted pair over K/F. It gives
   R, vR, E, smoothness and projectivity over F, regularity, the generic-point bijection
   with unchanged residue fields, the relative SNC and boundary assertions and parameters.
   Its construction passes to effective actions on each component, so no faithfulness
   is assumed, and it permits the empty divisor.
6. Surjectivity of the restricted quotient and h = q followed by d identify the image
   of D on the quotient with d inverse image of C. Pull back under vR to obtain both
   support equalities. The same set calculation applies when C is empty.
-/
theorem exists_semilinear_sylow_snc_resolution
    (e K : Type u) [Field e] [Field K] [Algebra e K] [Module.Finite e K]
    (ell : ℕ) (hell : ell.Prime) (hchar : ell ≠ ringChar e)
    (G : Type v) [Group G] [Finite G] (ρ : G →* (K ≃ₐ[e] K))
    (hfixed : IsPurelyInseparable e (IntermediateField.fixedField ρ.range))
    (B Y : Scheme.{u}) (b : B ⟶ Spec (.of e)) (p : Y ⟶ Spec (.of K))
    [Nonempty B] [IsProper b]
    (hBnormal : ∀ x : B, IsDomain (B.presheaf.stalk x) ∧
      IsIntegrallyClosed (B.presheaf.stalk x))
    (hBcomponents : ∃ (n : ℕ) (V : Fin n → B.Opens),
      (∀ i, IsIntegral (V i).toScheme) ∧ Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
      (⨆ i, V i) = ⊤)
    [Smooth p] [IsHProjective p] (a : G →* Aut Y)
    (hequivariant : ∀ g : G, (a g).hom ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom))
    (h : Y ⟶ B) (hbase : h ≫ b = p ≫ Spec.map (CommRingCat.ofHom (algebraMap e K)))
    (hinvariant : ∀ g : G, (a g).hom ≫ h = h)
    (hhprojective : IsProjectiveBundle h) (hhsurjective : Surjective h)
    (hhgeneric : ∀ y ∈ genericPoints Y,
      h y ∈ genericPoints B ∧ (h.residueFieldMap y).hom.Finite)
    (Q : Subgroup G → Scheme.{u}) (q : ∀ H : Subgroup G, Y ⟶ Q H)
    (hfinite : ∀ H : Subgroup G, IsFinite (q H))
    (hqsurjective : ∀ H : Subgroup G, Surjective (q H))
    (hqinv : ∀ (H : Subgroup G) (g : H), (a g).hom ≫ q H = q H)
    (hsections : ∀ (H : Subgroup G) (W : (Q H).Opens),
      Function.Injective ((q H).app W).hom ∧
      ∀ s : Γ(Y, q H ⁻¹ᵁ W),
        (s ∈ Set.range ((q H).app W).hom ↔
          ∀ (g : H) (O : Y.Opens) (hO : O ≤ q H ⁻¹ᵁ W)
            (hOg : O ≤ (a g).hom ⁻¹ᵁ (q H ⁻¹ᵁ W)),
            ((a g).hom.appLE (q H ⁻¹ᵁ W) O hOg).hom s =
              (Y.presheaf.map (homOfLE hO).op).hom s))
    (hcat : ∀ (H : Subgroup G) (T : Scheme.{u}) (f : Y ⟶ T),
      (∀ g : H, (a g).hom ≫ f = f) → ∃! r : Q H ⟶ T, q H ≫ r = f)
    (hgeom : ∀ (H : Subgroup G) (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
      Function.Surjective (fun t : Spec (.of Ω) ⟶ Y ↦ t ≫ q H) ∧
      ∀ t₁ t₂ : Spec (.of Ω) ⟶ Y, t₁ ≫ q H = t₂ ≫ q H ↔
        ∃ g : H, t₁ ≫ (a g).hom = t₂)
    (d : ∀ H : Subgroup G, Q H ⟶ B) (hd : ∀ H, q H ≫ d H = h)
    (hdense : ∃ V : B.Opens, Dense (V : Set B) ∧
      (∀ x ∈ genericPoints B, x ∈ V) ∧
      IsFinite ((d ⊤).resLE V ((d ⊤) ⁻¹ᵁ V) le_rfl) ∧
      (topologically IsHomeomorph).universally
        ((d ⊤).resLE V ((d ⊤) ⁻¹ᵁ V) le_rfl))
    (C : Set B) (hC : IsClosed C) (D : Y.IdealSheafData)
    (hD : D = ((Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩).comap h).radical)
    (hDsnc : D.IsSmoothStrictNormalCrossingsDivisor p) :
    ∃ (L : Subgroup G), (∃ n : ℕ, Nat.card L = ell ^ n) ∧
      Nat.Coprime L.index ell ∧
      ∃ (F : IntermediateField e K), F = IntermediateField.fixedField (L.map ρ) ∧
        Module.Finite e F ∧ Nat.Coprime (Module.finrank e F) ell ∧
        Module.Finite F K ∧ Algebra.IsSeparable F K ∧
        ∃ (sF : Q L ⟶ Spec (.of F)),
          q L ≫ sF = p ≫ Spec.map (CommRingCat.ofHom F.subtype) ∧
          ∃ U : (Q L).Opens, IsClosed (U : Set (Q L)) ∧
            (∃ A : Set (Set (Q L)), A ⊆ irreducibleComponents (Q L) ∧
              (U : Set (Q L)) = ⋃₀ A) ∧
            IsClosed (q L ⁻¹ᵁ U : Set Y) ∧
            IsProjectiveBundle (U.ι ≫ d L) ∧ Surjective (U.ι ≫ d L) ∧
            (q L ⁻¹ᵁ U).ι ≫ h =
              (q L).resLE U (q L ⁻¹ᵁ U) le_rfl ≫ (U.ι ≫ d L) ∧
            (∀ z ∈ genericPoints U.toScheme, (U.ι ≫ d L) z ∈ genericPoints B ∧
              ((U.ι ≫ d L).residueFieldMap z).hom.Finite ∧
              Nat.Coprime ((U.ι ≫ d L).residueDegree z) ell) ∧
            ∃ (R : Scheme.{u}) (rF : R ⟶ Spec (.of F)) (vR : R ⟶ U.toScheme),
              Smooth rF ∧ IsHProjective rF ∧ IsProjectiveBundle vR ∧ Surjective vR ∧
              vR ≫ (U.ι ≫ sF) = rF ∧
              Set.BijOn vR (genericPoints R) (genericPoints U.toScheme) ∧
              (∀ η ∈ genericPoints R, Function.Bijective (vR.residueFieldMap η).hom) ∧
              ∃ E : R.IdealSheafData, E.IsSmoothStrictNormalCrossingsDivisor rF ∧
                (E.support : Set R) = vR ⁻¹'
                  ((q L).resLE U (q L ⁻¹ᵁ U) le_rfl ''
                    ((q L ⁻¹ᵁ U).ι ⁻¹' (D.support : Set Y))) ∧
                (E.support : Set R) = (vR ≫ (U.ι ≫ d L)) ⁻¹' C ∧
                IsRegularScheme R ∧ IsStrictNormalCrossingsBoundary E ∧
                ∀ x : R, ∃ (W : R.affineOpens) (hx : x ∈ W.1)
                  (hN : IsNoetherianRing (R.presheaf.stalk x))
                  (t s : List (R.presheaf.stalk x)),
                  @IsLocalRing.IsRegularSystemOfParameters (R.presheaf.stalk x) _ _ hN t ∧
                  s.Sublist t ∧ s.Nodup ∧
                  (E.ideal W).map (R.presheaf.germ W.1 x hx).hom = Ideal.span {s.prod} := by
  sorry

end AlgebraicGeometry
