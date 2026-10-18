/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.AlgebraicGeometry.IndFiniteEtaleLocalSystem
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import Sheaf.CategoryTheory.Sites.EtaleContractedProductExists
import Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Free actions of torsion local systems

Source: ILO, Travaux de Gabber, Exposé XVII, Lemma 7.2.6, pp. 302–303
(blueprint: lem-per-torsion-torsor-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A free action of a torsion abelian local system with local-system quotient has
local-system total space. The action is written sectionwise, including its naturality.
The quotient `q : T ⟶ Y` is characterized by invariance and the universal property
for invariant maps to every set sheaf; it is the sheaf quotient, not the presheaf quotient.
Torsion is tested germ by germ, with no common exponent.

Source: ILO XVII, Lemma 7.2.6, pp. 302–303
(blueprint: lem-per-torsion-torsor-descent).

Proof: (1) Write Y as the filtered union of its finite local subsystems, pull these
back to T, and use ambient colimit closure (lem-per-set-local-system-calculus).
The empty quotient gives the empty total space. (2) Represent finite Y by a finite
étale X-scheme. It is Noetherian by finite type over a Noetherian base. The slice
site equivalence turns T into a torsor on Y. Pullback preserves the local-system
condition and torsion, the latter by the inverse-image stalk isomorphism
(lem-weil-pbc-inverse-image-stalk-germ). The finite étale total-space functor
preserves local systems, so it suffices to treat a torsor on a Noetherian base.
(3) Write G as a filtered union of finite subgroup systems
(lem-per-torsion-finite-subsystem). The base is quasi-compact and quasi-separated
by the locally Noetherian quasi-separatedness theorem. Filtered-colimit continuity
of H¹ and the torsor-class bijection descend the torsor class to a finite subgroup
G'. Coefficient functoriality and contracted-product existence identify T with
G ∧^{G'} T' for a G'-torsor T'. (4) For each finite subgroup H containing G', the
torsor H ∧^{G'} T' is étale locally a finite constant sheaf, hence represented by a
finite étale scheme (lem-galois-flc-representable). (5) These H are cofinal among
finite subgroup systems. The contracted-product universal property, tested against
an arbitrary set sheaf, identifies their filtered colimit with G ∧^{G'} T'. Thus T
is ind-finite étale, and the reductions in (1) and (2) finish the general case. -/
theorem isIndFiniteEtaleSheaf_of_free_torsion_action
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (T Y : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (vadd : ∀ U : X.Etaleᵒᵖ, G.obj.obj U → T.obj.obj U → T.obj.obj U)
    (hzero : ∀ (U : X.Etaleᵒᵖ) (t : T.obj.obj U), vadd U 0 t = t)
    (hadd : ∀ (U : X.Etaleᵒᵖ) (g h : G.obj.obj U) (t : T.obj.obj U),
      vadd U (g + h) t = vadd U g (vadd U h t))
    (hnat : ∀ {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U) (t : T.obj.obj U),
      T.obj.map f (vadd U g t) = vadd V (G.obj.map f g) (T.obj.map f t))
    (hfree : ∀ (U : X.Etaleᵒᵖ) (t : T.obj.obj U), Function.Injective (vadd U · t))
    (q : T ⟶ Y)
    (hqinvariant : ∀ (U : X.Etaleᵒᵖ) (g : G.obj.obj U) (t : T.obj.obj U),
      q.hom.app U (vadd U g t) = q.hom.app U t)
    (hquotient : ∀ (E : Sheaf X.smallEtaleTopology (Type (u + 1))) (f : T ⟶ E),
      (∀ (U : X.Etaleᵒᵖ) (g : G.obj.obj U) (t : T.obj.obj U),
        f.hom.app U (vadd U g t) = f.hom.app U t) →
      ∃! k : Y ⟶ E, q ≫ k = f)
    (hG : IsIndFiniteEtaleSheaf
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G))
    (htorsion : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
      (g : (pointedEtaleStalk G x : AddCommGrpCat.{u + 1})), ∃ n : ℕ, 0 < n ∧ n • g = 0)
    (hY : IsIndFiniteEtaleSheaf Y) : IsIndFiniteEtaleSheaf T := by
  sorry

end AlgebraicGeometry.Scheme
