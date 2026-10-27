module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Defs

/-! # Finite infinitesimal neighborhoods detect subgroup normalizers

Source: Conrad, Reductive group schemes, Proposition 2.1.6, pp.61--63,
and the proof of Theorem 2.3.6, p.74.
(blueprint: lem-sfb-finite-jet-normalizer-detection)

The neighborhood constructions below use the existing ideal-sheaf power and closed-subscheme
constructions. Equality under conjugation is tested on the represented functors on all schemes,
so includes the scheme structure and arbitrary further base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped MonObj

namespace AlgebraicGeometry
namespace GroupScheme

/-- The ideal of the nth neighborhood of the identity: the (n+1)st power of the
kernel of the identity section. Source: Conrad, Proposition 2.1.6 and Theorem 2.3.6.
(blueprint: lem-sfb-finite-jet-normalizer-detection). -/
noncomputable def identityNeighborhoodIdeal {S : Scheme.{u}} (K : Over S) [GrpObj K]
    (n : ℕ) : K.left.IdealSheafData :=
  (1 : Over.mk (𝟙 S) ⟶ K).left.ker ^ (n + 1)

/-- The closed identity neighborhood as an S-scheme, with its specified structural map.
Source: Conrad, Proposition 2.1.6 and Theorem 2.3.6.
(blueprint: lem-sfb-finite-jet-normalizer-detection). -/
noncomputable def identityNeighborhood {S : Scheme.{u}} (K : Over S) [GrpObj K]
    (n : ℕ) : Over S :=
  Over.mk ((identityNeighborhoodIdeal K n).subschemeι ≫ K.hom)

/-- The actual closed inclusion of the identity neighborhood into the group scheme.
Source: Conrad, Theorem 2.3.6, p.74.
(blueprint: lem-sfb-finite-jet-normalizer-detection). -/
noncomputable def identityNeighborhoodι {S : Scheme.{u}} (K : Over S) [GrpObj K]
    (n : ℕ) : identityNeighborhood K n ⟶ K :=
  Over.homMk (identityNeighborhoodIdeal K n).subschemeι

/-- The identity section after arbitrary base change, defined by the pullback universal property.
Source: Conrad, Proposition 2.1.6, pp.62--63.
(blueprint: lem-sfb-finite-jet-normalizer-detection). -/
noncomputable def baseChangedIdentity {S : Scheme.{u}} (K : Over S) [GrpObj K]
    (W : Over S) : W.left ⟶ pullback K.hom W.hom :=
  pullback.lift (W.hom ≫ (1 : Over.mk (𝟙 S) ⟶ K).left) (𝟙 W.left)
    (by simp only [Category.assoc, Over.w, Over.mk_hom, Category.comp_id,
      Category.id_comp])

/-- The canonical base change of an arrow of S-schemes, preserving both projections.
Source: Conrad, Theorem 2.3.6, p.74, base change of the jet quotient.
(blueprint: lem-sfb-finite-jet-normalizer-detection). -/
noncomputable def baseChangedArrow {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y)
    (W : Over S) : pullback X.hom W.hom ⟶ pullback Y.hom W.hom :=
  pullback.map X.hom W.hom Y.hom W.hom i.left (𝟙 W.left) (𝟙 S)
    (by simp only [Category.comp_id, Over.w]) (by simp)

/-- Smooth affine group schemes and their smooth geometrically connected closed subgroups
have finite locally free identity neighborhoods; finitely many affine charts and finite orders
suffice to detect the normalizer, universally on test schemes.

Source: Conrad, Proposition 2.1.6, pp.61--63, and Theorem 2.3.6 proof, p.74.
(blueprint: lem-sfb-finite-jet-normalizer-detection).

Proof plan (the nine steps of the DAG node):
1. Apply lem-sfb-smooth-section-finite-jets to both identity sections. The quotients
   are finite locally free and commute with base change. Their coordinate modules are
   locally free by lem-pc-finite-flat-pushforward-locally-free applied to the structure sheaf.
2. For the surjection B to D of coordinate rings, the augmentation ideals satisfy
   q(J_G) = J_H. Hence D/J_H^(n+1) is B/(ker q + J_G^(n+1)), a quotient of B/J_G^(n+1).
   Also H intersect G_m = H_m and H_n intersect G_m = H_m for m at most n.
   Conjugation fixes the identity and therefore preserves every ambient ideal power.
3. Use lem-sfb-smooth-connected-subgroup-noetherian-model to descend the finitely
   presented group and subgroup data to a Noetherian base. Keep arbitrary test schemes.
4. Apply lem-sfb-finite-locally-free-source-factorization-locus to conjugation and
   inverse conjugation of H_n into H. The sum of the two defining ideals cuts out N_n.
   Unique affine quotient factorizations glue by lem-weil-pbc-scheme-morphism-gluing.
5. The intersection calculations of step 2 identify N_n with the equality stabilizer
   of H_n, and show N_n is contained in N_m for m at most n, scheme-theoretically.
6. For an element of every N_n, the inverse image of H under conjugation of H is
   closed by lem-weil-pbc-closed-immersion-base-change and contains every H_n.
   Apply lem-sfb-smooth-section-universal-jet-density to obtain containment of H,
   then use inverse conjugation to obtain equality. The converse follows from step 2.
7. By pqf-lem-affine-open-locnoeth the ambient coordinate ring is Noetherian.
   Finite generation of the sum of the increasing defining ideals makes it equal
   to one of them. Thus a single positive order detects the normalizer on all tests.
8. Pull back from the Noetherian model. The identity-neighborhood identifications
   of step 1 give the same detection equivalence after arbitrary base change.
9. Simultaneously trivialize the two finite locally free coordinate modules on
   principal affine opens; quasi-compactness selects a finite subcover. On nonempty
   charts the augmentation gives r at least 1 and the quotient gives r at most M.
   For the empty base use the empty cover. Quotients and bases survive base change.
-/
theorem finiteJet_normalizer_detection
    (A : CommRingCat.{u}) (G H : Over (Spec A)) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [Smooth G.hom] [LocallyOfFinitePresentation G.hom]
    (i : H ⟶ G) [IsMonHom i] [IsClosedImmersion i.left]
    [LocallyOfFinitePresentation i.left] [Smooth H.hom] [GeometricallyConnected H.hom] :
    (∀ (n : ℕ), 1 ≤ n →
      (identityNeighborhood G n).hom.IsFiniteLocallyFree ∧
      (identityNeighborhood H n).hom.IsFiniteLocallyFree) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (W : Over (Spec A)),
      (baseChangedIdentity G W).ker ^ (n + 1) =
        (identityNeighborhoodIdeal G n).comap (pullback.fst G.hom W.hom) ∧
      (baseChangedIdentity H W).ker ^ (n + 1) =
        (identityNeighborhoodIdeal H n).comap (pullback.fst H.hom W.hom)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (W : Over (Spec A)) (g : W ⟶ G),
      ∀ (V : Over (Spec A)) (v : V ⟶ W),
        Set.range (fun h : V ⟶ identityNeighborhood G n ↦
          (v ≫ g) * (h ≫ identityNeighborhoodι G n) * (v ≫ g)⁻¹) =
        Set.range (fun h : V ⟶ identityNeighborhood G n ↦ h ≫ identityNeighborhoodι G n)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∃ j : identityNeighborhood H n ⟶ identityNeighborhood G n,
      j ≫ identityNeighborhoodι G n = identityNeighborhoodι H n ≫ i ∧
      IsClosedImmersion j.left ∧ Function.Surjective j.left.appTop.hom ∧
      ∀ (W : Over (Spec A)) (_ : IsAffine W.left),
        Function.Surjective (baseChangedArrow j W).appTop.hom) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ s : Spec A,
      ∃ U : (Spec A).affineOpens, s ∈ U.1 ∧ ∃ M r : ℕ,
        Nonempty (@Module.Basis (Fin M) Γ(U.1.toScheme, ⊤)
          Γ(pullback (identityNeighborhood G n).hom U.1.ι, ⊤)
          inferInstance inferInstance
          (pullback.snd (identityNeighborhood G n).hom U.1.ι).appTop.hom.toModule) ∧
        Nonempty (@Module.Basis (Fin r) Γ(U.1.toScheme, ⊤)
          Γ(pullback (identityNeighborhood H n).hom U.1.ι, ⊤)
          inferInstance inferInstance
          (pullback.snd (identityNeighborhood H n).hom U.1.ι).appTop.hom.toModule)) ∧
    ∃ (k : ℕ) (U : Fin k → (Spec A).affineOpens) (n M r : Fin k → ℕ),
      (∀ s : Spec A, ∃ a : Fin k, s ∈ (U a).1) ∧
      ∀ a : Fin k, 1 ≤ n a ∧ 1 ≤ r a ∧ r a ≤ M a ∧
        Nonempty (@Module.Basis (Fin (M a)) Γ((U a).1.toScheme, ⊤)
          Γ(pullback (identityNeighborhood G (n a)).hom (U a).1.ι, ⊤)
          inferInstance inferInstance
          (pullback.snd (identityNeighborhood G (n a)).hom (U a).1.ι).appTop.hom.toModule) ∧
        Nonempty (@Module.Basis (Fin (r a)) Γ((U a).1.toScheme, ⊤)
          Γ(pullback (identityNeighborhood H (n a)).hom (U a).1.ι, ⊤)
          inferInstance inferInstance
          (pullback.snd (identityNeighborhood H (n a)).hom (U a).1.ι).appTop.hom.toModule) ∧
        ∀ (W : Over (Spec A)),
          (∃ w : W.left ⟶ (U a).1.toScheme, w ≫ (U a).1.ι = W.hom) →
          ∀ g : W ⟶ G,
            (∀ (V : Over (Spec A)) (v : V ⟶ W),
              Set.range (fun h : V ⟶ identityNeighborhood H (n a) ↦
                (v ≫ g) * (h ≫ identityNeighborhoodι H (n a) ≫ i) * (v ≫ g)⁻¹) =
              Set.range (fun h : V ⟶ identityNeighborhood H (n a) ↦
                h ≫ identityNeighborhoodι H (n a) ≫ i)) ↔
            (∀ (V : Over (Spec A)) (v : V ⟶ W),
              Set.range (fun h : V ⟶ H ↦ (v ≫ g) * (h ≫ i) * (v ≫ g)⁻¹) =
              Set.range (fun h : V ⟶ H ↦ h ≫ i)) := by
  sorry

end GroupScheme
end AlgebraicGeometry
