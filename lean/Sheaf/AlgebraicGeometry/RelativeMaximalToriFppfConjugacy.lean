module

public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.NoetherianDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf

/-! # Fppf local conjugacy of geometrically maximal tori

Source: Conrad, Reductive Group Schemes, proof of Theorem 3.2.6, pp.94--95,
and Proposition 2.1.2 / Corollary 2.1.5, pp.56--61
(blueprint: lem-sfb-relative-maximal-tori-fppf-conjugacy).

The two tori are indexed by `Fin 2`. Geometric maximality is written out as the
absence of a proper inclusion into any split torus subgroup of the geometric fibre.
The conclusion tests subgroup equality on every scheme over each cover member.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- Two geometrically maximal relative tori in a smooth affine finitely presented
 group scheme are fppf locally conjugate, as subgroup functors on all test schemes.
Source: Conrad, Reductive Group Schemes, proof of Theorem 3.2.6, pp.94--95,
and Proposition 2.1.2 / Corollary 2.1.5, pp.56--61
(blueprint: lem-sfb-relative-maximal-tori-fppf-conjugacy).

Proof:
1. It suffices to construct the required covering after an fppf covering of the base: compose the
local coverings, using the covering transitivity axiom. First cover S by affine opens. On each such
open, the definition of a relative torus supplies splitting fppf coverings for T_0 and T_1; pull one
back along the other and compose. Refine by the affine-refinement lemma. Thus we may work over a
nonempty affine S=Spec A on which T_a is identified with the split torus of rank r_a, for a=0,1. The
empty affine needs no covering members. Base change preserves smoothness of G. Geometric maximality
is inherited because every algebraically closed geometric point of any new base is also such a point
of the original base. Uses: def-sfb-relative-torus, def-pc-fppf-site, def-weil-pbc-sites-and-
cohomology, lem-trf-fppf-covering-base-change, lem-pc-fppf-affine-refinement, lem-pc-proper-base-
change.

2. Write G=Spec C. The affine smoothness equivalence identifies A to C as a smooth ring map. The
smooth-algebra model theorem gives a finitely generated integer subring A_0 of A and a smooth affine
finite-presentation scheme G_0=Spec C_0 whose base change is G. Enlarge A_0 through the directed set
of finitely generated subrings of A when necessary, replacing G_0 by base change; smoothness
persists. This directed system has limit Spec A by Noetherian approximation. Every stage is
Noetherian by the finite-type-over-Z lemma, and every scheme used as a finite product of G_0 and
split tori is affine, hence qcqs. Uses: lem-weil-pbc-smooth-ring-map-iff-smooth-affine, lem-weil-
pbc-smooth-algebra-finite-type-model, lemma-nagata-noetherian-inverse-system-affine, lem-weil-pbc-
finite-type-over-noetherian, lem-weil-pbc-affine-scheme-qcqs, lem-pc-proper-base-change.

3. Descend the multiplication, identity and inverse of G, and both maps from the standard split tori
into G, by the arrow clause of finite-presentation spreading out. Use the standard split tori and
the finite products of G_0 as the chosen object models. The associativity, unit, inverse and
subgroup-homomorphism diagrams are finitely many equalities of maps between those finite-
presentation models. The equality clause therefore makes all diagrams hold at a common later stage.
The two descended torus maps are locally of finite type (their affine source algebras have finite
generating sets already over the base); the closed-immersion descent lemma makes both maps closed
immersions after a further enlargement. We now have a smooth affine finite-type group G_0 over a
nonzero Noetherian ring A_0, with closed split torus subgroups T_{0,0},T_{1,0}, whose entire diagram
pulls back to the prescribed one. No geometric maximality assertion at this stage is needed. Uses:
thm-pd-spreading-out, lem-weil-pbc-descend-closed-immersion.

4. Apply the existing multiplicative-type transporter theorem to G_0 and the two split tori. It
gives a closed finite-presentation smooth A_0-scheme Z_0 representing gT_{0,0}g^{-1} contained in
T_{1,0}. Pull back along Spec A to Spec A_0. Its arbitrary-base-change assertion says exactly that
Z=Z_0 times_{A_0} A represents g(T_0)_Vg^{-1} contained in (T_1)_V, as subgroup functors on every
V-scheme. In particular there is a universal g in G(Z) and a unique induced group homomorphism
q:(T_0)_Z to (T_1)_Z, with j_1 q=Int(g)j_0. The group diagrams follow since j_1 is monic. Smoothness
of Z over S follows from smooth base change. Uses: lem-sfb-multiplicative-type-transporter-smooth,
lem-pc-proper-base-change.

5. For each geometric point s:Spec Omega to S, consider G_s. Its identity component G_s^0 is an open
and closed connected subgroup of finite type. It is affine by the closed-immersion affine criterion
and smooth by restriction of the smooth morphism G_s to its open component. Each split torus (T_a)_s
is connected: its Laurent coordinate ring over Omega is a domain (including rank zero), so its
spectrum is irreducible. Its image contains the identity and therefore lies in the identity
component. Factor through that open component by the open-factorization lemma; the torus remains a
closed subgroup there. A larger torus in G_s^0 would be a larger torus in G_s, so both tori are
maximal in G_s^0. The classical Borel/maximal-torus conjugacy theorem, applied to this smooth
connected affine Omega-group, supplies h in G_s^0(Omega) with h(T_0)_s h^{-1}=(T_1)_s as subgroup
schemes. Consequently h defines an Omega-point of Z above s. Every point of S admits an
algebraically closed residue-field extension, so Z to S is surjective. Uses: lem-sfb-finite-type-
group-identity-subgroup, lem-weil-pbc-closed-immersion-affine-cover-criterion, lem-weil-pbc-smooth-
restrict-open-subschemes, lem-weil-pbc-morphism-factors-through-open-subscheme, lem-sfb-borel-
maximal-torus-conjugacy.

6. The universal containment is an equality on Z, not just on its geometric points. Indeed, at every
algebraically closed geometric point z of Z, q_z identifies the conjugate of the maximal torus
(T_0)_z with a torus subgroup of (T_1)_z. Maximality in G_z makes this inclusion an equality. Apply
the split-torus matrix-sheaf theorem to q over Z. Locally on Z it is given by a constant integer
matrix M. If that open is nonempty, choose a geometric point of it. Since q_z is an isomorphism, the
matrix correspondence and its composition law give an integer inverse of M there: r_0=r_1 and M is
unimodular. The same constant inverse defines an inverse homomorphism throughout that open. These
local inverses agree because they are inverses of q, so q is an isomorphism. Thus j_1 q=Int(g)j_0
gives g(T_0)_Zg^{-1}=(T_1)_Z as subgroup functors on every Z-scheme, with no reducedness assumption.
Uses: lem-sfb-relative-split-torus-matrix-sheaf.

7. The smooth surjection Z to S is flat and locally of finite presentation by the smooth-flat lemma.
By the definition of the fppf site, its singleton is an fppf covering. Its universal element g gives
the required conjugation by step 6. For the original base, compose these coverings with the affine
splitting coverings of step 1, using site transitivity. Empty pieces contribute no members. Ranks
are fixed only on each splitting member; the construction requires no global rank, connectedness of
G, reductivity or Noetherian condition on S. Uses: lem-pc-smooth-flat, def-pc-fppf-site, def-weil-
pbc-sites-and-cohomology. -/
theorem relative_maximal_tori_fppf_conjugacy
    {S : Scheme.{u}} (G : Grp (Over S))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    (T : Fin 2 → Grp (Over S)) (j : ∀ a : Fin 2, T a ⟶ G)
    [∀ a : Fin 2, IsClosedImmersion (j a).hom.hom.left]
    (hT : ∀ a : Fin 2, IsRelativeTorus (T a).X)
    (hmax : ∀ (a : Fin 2) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S) (H : Grp (Over (Spec (.of Ω))))
      (i : H ⟶ (Over.pullback s).mapGrp.obj G),
      IsClosedImmersion i.hom.hom.left →
      (∃ r : ℕ, Nonempty (yonedaGrpObj H.X ≅ relativeSplitTorusFunctor (Spec (.of Ω)) r)) →
      ∀ f : (Over.pullback s).mapGrp.obj (T a) ⟶ H,
        f ≫ i = (Over.pullback s).mapGrp.map (j a) → IsIso f) :
    ∃ (I : Type u) (U : I → Over S) (g : ∀ i : I, U i ⟶ G.X),
      Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        Scheme.fppfPrecoverage S ∧
      ∀ (i : I) (V : Over S) (v : V ⟶ U i),
        Set.range (fun t : V ⟶ (T 0).X ↦
          (v ≫ g i) * (t ≫ (j 0).hom.hom) * (v ≫ g i)⁻¹) =
        Set.range (fun t : V ⟶ (T 1).X ↦ t ≫ (j 1).hom.hom) := by
  sorry

end AlgebraicGeometry
