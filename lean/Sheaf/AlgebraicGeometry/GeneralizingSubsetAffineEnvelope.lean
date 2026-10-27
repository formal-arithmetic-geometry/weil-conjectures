module

public import Sheaf.AlgebraicGeometry.RingedSubspace
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.Topology.SpectralGeneralizations
import Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding
import Sheaf.AlgebraicGeometry.QcOpenIntersectionSpectralPresentation
import Sheaf.Topology.SpectralDirectedLimit
import Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange
import WeilConjectures.Topology.InverseImageStalk
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Localization

/-!
# Affine envelopes of generalizing retrocompact subsets

Source: Raynaud, Un critère d'effectivité de descente, §2, Propositions 2.3(ii)--(iii),
2.4(A)--(B), Corollary 2.5(i)--(ii), and Theorem 3.3, proof 4°.
(blueprint: lem-sfb-generalizing-subset-affine-envelope)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.GeneralizingSubset

/-- The section ring of the specified inverse-image ringed subspace, not sections on an
arbitrarily chosen scheme structure. Source: Raynaud §2, Proposition 2.3(ii).
(blueprint: lem-sfb-generalizing-subset-affine-envelope) -/
noncomputable def sections (A : CommRingCat.{u}) (H : Set (Spec A)) : CommRingCat.{u} :=
  (LocallyRingedSpace.ringedSubspace (Spec A).toLocallyRingedSpace H).presheaf.obj (op ⊤)

/-- The canonical affine envelope of the specified ringed subspace.
Source: Raynaud §2, Proposition 2.3(ii).
(blueprint: lem-sfb-generalizing-subset-affine-envelope) -/
noncomputable def envelope (A : CommRingCat.{u}) (H : Set (Spec A)) : Scheme.{u} :=
  Spec (sections A H)

/-- The map of envelopes induced by restriction from A to the subspace's section ring.
Source: Raynaud §2, Proposition 2.3(ii).
(blueprint: lem-sfb-generalizing-subset-affine-envelope) -/
noncomputable def map (A : CommRingCat.{u}) (H : Set (Spec A)) : envelope A H ⟶ Spec A :=
  Spec.map (toSpecΓ A ≫
    (LocallyRingedSpace.ringedSubspaceι (Spec A).toLocallyRingedSpace H).hom.c.app (op ⊤))

/-- The same inverse-image ringed subspace bundled using locality proof data only.
Source: Raynaud §2, Proposition 2.3(ii); Stacks Tag 0API.
(blueprint: lem-sfb-generalizing-subset-affine-envelope) -/
noncomputable def space (A : CommRingCat.{u}) (H : Set (Spec A))
    (hl : ∀ x : H, IsLocalRing
      ((LocallyRingedSpace.ringedSubspace (Spec A).toLocallyRingedSpace H).presheaf.stalk x)) :
    LocallyRingedSpace.{u} :=
  LocallyRingedSpace.locallyRingedSubspace (Spec A).toLocallyRingedSpace H hl

/-- The canonical locally ringed map whose normalized global-section map is the identity.
Source: Raynaud §2, Proposition 2.3(ii); Stacks Tag 01I1.
(blueprint: lem-sfb-generalizing-subset-affine-envelope) -/
noncomputable def unit (A : CommRingCat.{u}) (H : Set (Spec A))
    (hl : ∀ x : H, IsLocalRing
      ((LocallyRingedSpace.ringedSubspace (Spec A).toLocallyRingedSpace H).presheaf.stalk x)) :
    space A H hl ⟶ (envelope A H).toLocallyRingedSpace :=
  (space A H hl).toΓSpec

/-- The image of the specified canonical map, used to form the boundary.
Source: Raynaud §2, Proposition 2.4.
(blueprint: lem-sfb-generalizing-subset-affine-envelope) -/
noncomputable def image (A : CommRingCat.{u}) (H : Set (Spec A))
    (hl : ∀ x : H, IsLocalRing
      ((LocallyRingedSpace.ringedSubspace (Spec A).toLocallyRingedSpace H).presheaf.stalk x)) :
    Set (envelope A H) :=
  Set.range (unit A H hl).base

/-- The image in the original spectrum of the complement of the canonical image.
Source: Raynaud §2, Proposition 2.4(A).
(blueprint: lem-sfb-generalizing-subset-affine-envelope) -/
noncomputable def boundary (A : CommRingCat.{u}) (H : Set (Spec A))
    (hl : ∀ x : H, IsLocalRing
      ((LocallyRingedSpace.ringedSubspace (Spec A).toLocallyRingedSpace H).presheaf.stalk x)) :
    Set (Spec A) :=
  map A H '' (image A H hl)ᶜ

/-- The inverse image of H in the spectrum of the actual stalk at s.
Source: Raynaud §2, Proposition 2.3(iii).
(blueprint: lem-sfb-generalizing-subset-affine-envelope) -/
def localSubset (A : CommRingCat.{u}) (H : Set (Spec A)) (s : Spec A) :
    Set (Spec ((Spec A).presheaf.stalk s)) :=
  (Spec A).fromSpecStalk s ⁻¹' H

/-- Affine envelope, boundary criterion, and compatibility with localization at every point.
Source: Raynaud §2, Propositions 2.3(ii)--(iii), 2.4(A)--(B), Corollary 2.5(i)--(ii),
and Theorem 3.3, proof 4° (blueprint: lem-sfb-generalizing-subset-affine-envelope).

Proof:
1. An affine scheme is qcqs and spectral. Retrocompactness makes H compact; stability
   under generalization identifies H with the intersection of its compact open neighborhoods
   (lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-scheme-spectral,
   lem-weil-pbc-spectral-generalizations-of-quasi-compact). This family contains the whole
   scheme and is closed under finite intersections, including when H is empty.
2. Apply lem-a1-intersection-canonical-affine-embedding to this family. The inverse-image
   stalk isomorphisms give locality. The affine adjunction gives the normalized unit and
   identifies its image with the induced ringed subspace. Both composites to Spec A induce
   the same restriction map on sections, so the composite is the canonical inclusion.
3. For any localization of A, inverse images of compact opens are finite unions of principal
   opens. The compact-open intersection spectral presentation and spectral directed-limit
   theorem make the inverse-image subset retrocompact and generalizing. This applies at s.
4. Apply lem-a1-intersection-sections-flat-base-change. The canonical section comparison is
   C tensor_A A' isomorphic to C'. The affine fibre-product formula identifies its spectrum
   with the pullback, with the two prescribed projections and the induced subspace map.
5. Tensoring with a localization localizes C at the image of the denominators, by the tensor
   pushout and localization universal properties. Prime correspondence identifies the first
   projection with the embedding onto points lying over generalizations of s.
6. For s in H its generalizations lie in H, so H_s is the whole local spectrum. Its envelope
   is that spectrum. Thus h has just the point k(s) above s, proving h inverse H = k(H).
   Apply this also locally and use the embedding in Step 5: the canonical image pulls back,
   and a point outside it lies over t precisely when a point outside k(H) lies over c_s(t).
   This proves the equality of boundary images, not just an inclusion.
7. If E is a scheme, the inclusion's stalk maps are the inverse-image stalk isomorphisms,
   hence flat. Retrocompactness makes it quasi-compact. Injectivity on points and the
   inverse-image adjunction make it a monomorphism, with exactly the specified sheaf map.
8. By lem-sfb-qc-flat-monomorphism-affine-neighbourhood the inclusion is affine over an open
   neighborhood of H. Principal affine neighborhoods inside it have affine inverse images.
   Step 4 identifies their envelopes with the inverse images in V, so their union avoids
   the boundary image B. Its closed complement contains closure B and misses H.
9. Conversely, U = S minus closure B contains H. The equality h inverse H = k(H) and the
   definition of B show k(H) = h inverse U. Hence it is open in V and Step 2 makes E an
   open subscheme, proving the converse and allowing Step 7 to apply.
10. The isomorphism with the induced ringed image makes a surjective k an isomorphism.
    An isomorphism to V makes E affine; for an affine E the affine adjunction makes its
    canonical unit an isomorphism. Isomorphisms are surjective, including for Spec of zero.
-/
theorem affine_envelope (A : CommRingCat.{u}) (H : Set (Spec A))
    (hgen : ∀ (s : Spec A), s ∈ H → ∀ (t : Spec A), t ⤳ s → t ∈ H)
    (hretro : IsRetrocompact H) :
    ∃ hl : ∀ x : H, IsLocalRing
      ((LocallyRingedSpace.ringedSubspace (Spec A).toLocallyRingedSpace H).presheaf.stalk x),
      (toSpecΓ (sections A H) ≫ (unit A H hl).c.app (op ⊤) = 𝟙 _) ∧
      (∃ e : (space A H hl).toSheafedSpace ≅
          LocallyRingedSpace.ringedSubspace (envelope A H).toLocallyRingedSpace (image A H hl),
        e.hom ≫ LocallyRingedSpace.ringedSubspaceι
          (envelope A H).toLocallyRingedSpace (image A H hl) = (unit A H hl).toShHom) ∧
      ((unit A H hl).toShHom ≫ (map A H).toLRSHom.toShHom =
        LocallyRingedSpace.ringedSubspaceι (Spec A).toLocallyRingedSpace H) ∧
      (map A H ⁻¹' H = image A H hl) ∧
      ((∃ X : Scheme.{u}, Nonempty (X.toLocallyRingedSpace ≅ space A H hl)) ↔
        closure (boundary A H hl) ∩ H = ∅) ∧
      (∀ (X : Scheme.{u}) (e : X.toLocallyRingedSpace ≅ space A H hl),
        ∃ f : X ⟶ Spec A,
          f.toLRSHom.toShHom = e.hom.toShHom ≫
            LocallyRingedSpace.ringedSubspaceι (Spec A).toLocallyRingedSpace H ∧
          QuasiCompact f ∧ Flat f ∧ Mono f) ∧
      (Function.Surjective (unit A H hl).base ↔ IsIso (unit A H hl)) ∧
      (IsIso (unit A H hl) ↔ ∃ X : Scheme.{u},
        IsAffine X ∧ Nonempty (X.toLocallyRingedSpace ≅ space A H hl)) ∧
      (∀ s : Spec A,
        (∀ t ∈ localSubset A H s, ∀ z, z ⤳ t → z ∈ localSubset A H s) ∧
        IsRetrocompact (localSubset A H s) ∧
        ∃ hls : ∀ x : localSubset A H s, IsLocalRing
            ((LocallyRingedSpace.ringedSubspace
              (Spec ((Spec A).presheaf.stalk s)).toLocallyRingedSpace
              (localSubset A H s)).presheaf.stalk x),
        ∃ q : space ((Spec A).presheaf.stalk s) (localSubset A H s) hls ⟶ space A H hl,
          (∀ x, (q.base x).val = (Spec A).fromSpecStalk s x.val) ∧
          (q.toShHom ≫ LocallyRingedSpace.ringedSubspaceι (Spec A).toLocallyRingedSpace H =
            LocallyRingedSpace.ringedSubspaceι
              (Spec ((Spec A).presheaf.stalk s)).toLocallyRingedSpace (localSubset A H s) ≫
                ((Spec A).fromSpecStalk s).toLRSHom.toShHom) ∧
          ∃ e : envelope ((Spec A).presheaf.stalk s) (localSubset A H s) ≅
              pullback (map A H) ((Spec A).fromSpecStalk s),
            (e.hom ≫ pullback.fst (map A H) ((Spec A).fromSpecStalk s) =
              Spec.map (LocallyRingedSpace.Γ.map q.op)) ∧
            (e.hom ≫ pullback.snd (map A H) ((Spec A).fromSpecStalk s) =
              map ((Spec A).presheaf.stalk s) (localSubset A H s)) ∧
            (image ((Spec A).presheaf.stalk s) (localSubset A H s) hls =
              (e.hom ≫ pullback.fst (map A H) ((Spec A).fromSpecStalk s)) ⁻¹' image A H hl) ∧
            (boundary ((Spec A).presheaf.stalk s) (localSubset A H s) hls =
              (Spec A).fromSpecStalk s ⁻¹' boundary A H hl)) := by
  sorry

end AlgebraicGeometry.GeneralizingSubset
