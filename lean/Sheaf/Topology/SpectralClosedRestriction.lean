module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Sheaves.Functors

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Etale Cohomology, Lemma 59.82.1 (Tag 09ZG).
(blueprint: lem-weil-pbc-h0-spectral-closed-restriction)
 Proof (Stacks 09ZG): (1) restriction commutes with sheaf morphisms and is identified
 on stalks with the inverse-image stalk bijection. Every point of X specializes to Z,
 so equality on Z gives equality on all stalks and injectivity. (2) For a finite constant
 sheaf, restriction of locally constant maps is bijective by induction on the number of
 values, using the connectedness hypothesis and the clopen decomposition lift (0CAM).
 (3) The same holds for finite products of pushed-forward finite constant sheaves, by
 finite-product compatibility and the closed-subspace spectrality lemma. (4) A subsheaf
 injecting sectionwise into such a product has surjective restriction: lift locally on
 stalks, then glue using sectionwise injectivity. (5) Express an arbitrary sheaf as a
 filtered colimit of these subsheaves; restriction and sections commute with the colimit
 on the spectral closed subspace, yielding surjectivity. Together with (1), the map is
 bijective. These steps use the proof dependencies recorded in the DAG node.
-/
theorem spectral_closed_restriction
    (X : TopCat.{u}) [SpectralSpace X]
    (Z : Set X) (hZ : IsClosed Z)
    (hconn : ∀ x : X, ConnectedSpace (↥(Z ∩ closure ({x} : Set X))))
    (F : X.Sheaf (Type u)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let R := (Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F
    Function.Bijective
      (fun s : F.1.obj (op ⊤) =>
        (R.1.app (op ⊤)) s) := by
  sorry

end TopCat
