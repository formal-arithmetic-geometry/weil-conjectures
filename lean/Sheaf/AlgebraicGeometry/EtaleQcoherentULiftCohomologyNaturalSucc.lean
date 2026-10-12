module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherent
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy

/-! # Positive-degree naturality of coefficient universe lift

Source: Stacks Project, Tag 03P2, separated-case affine-cover argument.
(blueprint: lem-sc-etale-qcoherent-ulift-cohomology-natural-succ)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The positive-degree naturality part of coefficient comparison.
Source: Stacks Project, Tag 03P2, separated-case finite affine cover proof.
(blueprint: lem-sc-etale-qcoherent-ulift-cohomology-natural-succ)

Proof: Fix a finite affine open cover of X, which exists by quasi-compactness.
Every nonempty finite intersection is affine by separatedness. Restriction of
E to such an intersection is the associated sheaf of the pulled-back module,
which remains quasi-coherent. Ordinary and lifted affine acyclicity therefore
make the positive rows of both Čech-to-derived spectral sequences vanish.
Their edge maps identify H^(n+1) with the corresponding section-complex homology.
For naturality, lift theta to a map of an injective resolution in each coefficient
universe. The induced maps of the Čech double complexes commute with both the
augmentation from sections of the resolution and the augmentation from the
section Čech complex of E. Hence the edge maps intertwine theta. Two resolution
lifts are homotopic and give the same homology maps, so the edge maps depend on
neither lift. This does not compare injective objects across universes.

For each Čech degree the tuples from the fixed finite cover form a finite set.
Lowering each lifted section defines an additive equivalence of the products;
its inverse lifts every component. These maps commute with restrictions, so
with every signed summand in the alternating differential. They also commute
with each component of theta, since the lifted component sends up(s) to
up(theta(s)). Thus they identify cocycles and coboundaries, inducing mutually
inverse additive maps on homology that intertwine theta. Compose with the two
edge isomorphisms to obtain e. The cover and all three isomorphisms are fixed
before theta is introduced, so the same e works for all theta. Computing small
coefficient Ext with HasExt.standard instead of another universe is reindexing
via Ext.homAddEquiv; the reindexing commutes with postcomposition, hence with
Sheaf.H.map. No O-linear hypothesis on theta is used. An empty scheme permits
the empty cover and gives zero complexes; the zero module does likewise.
-/
theorem exists_etaleTensorSectionsSheaf_cohomology_ulift_natural_succ
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    let E := etaleTensorSectionsSheaf F
    let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
    ∃ e : Sheaf.H (L.obj E) (n + 1) ≃+
        @Sheaf.H _ _ X.smallEtaleTopology E inferInstance (HasExt.standard _) (n + 1),
      ∀ (θ : E ⟶ E) (x : Sheaf.H (L.obj E) (n + 1)),
        e (Sheaf.H.map (L.map θ) (n + 1) x) =
          @Sheaf.H.map.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology
            inferInstance (HasExt.standard _)
            _ _ θ (n + 1) (e x) := by sorry

end AlgebraicGeometry.Scheme.Modules
