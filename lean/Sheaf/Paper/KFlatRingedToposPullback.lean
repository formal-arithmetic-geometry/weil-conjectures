/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Algebra.Homology.FilteredColimitsTensor
import Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Algebra.Homology.FlatTruncationTower
import Sheaf.Algebra.Homology.AcyclicKFlatCyclesFlat
/-!
# Ringed-topos pullback preserves K-flat complexes with flat terms
Source: Stacks Project, Cohomology on Sites, Tag 0G7E, lemma-pullback-K-flat
(blueprint: lem-weil-pbc-ringed-topos-kflat-pullback).
-/
@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
/-- Termwise pullback along a morphism of ringed topoi preserves K-flatness and flat
terms. Source: Stacks Project, Tag 0G7E, lemma-pullback-K-flat
(blueprint: lem-weil-pbc-ringed-topos-kflat-pullback).
`I` presents the algebraic inverse image of rings and modules along `uInv`. The equations
`hobj` and `hmap` identify the additive functor `uStar` with inverse image followed by
extension of scalars along `c`, on objects and morphisms. Additivity is the structure of
this module pullback, used to apply it termwise. No flatness of `c` is assumed.
Proof plan (Stacks 0G7E):
1. Apply [lem-weil-pbc-ringed-topos-flat-module-pullback] to each K^q. Thus every u^*K^q is
flat. It remains to prove K-flatness.
2. Record two filtered-colimit consequences used below. By [lem-pc-module-filtered-colimits-
tensor], cohomology commutes with sequential degreewise colimits (exact colimits commute with
kernels and images), and total tensor commutes with these colimits. Thus a sequential colimit of
K-flat complexes is K-flat: for an acyclic F, each \operatorname{Tot}(F\otimes P_n) has zero
cohomology, and so does its colimit. Likewise a sequential colimit of flat module sheaves is
flat: put the variable modules and the fixed tensor factor in degree zero in the cited tensor
comparison, and take the colimit of the short exact sequences obtained by tensoring an arbitrary
short exact sequence with the flat modules. The reversed order of total tensor is identified
explicitly by the degreewise swap x\otimes y\mapsto(-1)^{pq}y\otimes x on degrees (p,q); its
signs commute with the total differential. Thus the cited colimit formula, written with the
colimit in the first factor, also applies to the second factor used in the K-flat definition.
3. Every bounded-above flat-term complex P on either site is K-flat. For an arbitrary acyclic
complex F, its good truncations \tau_{\le m}F are bounded above and acyclic, and their
degreewise colimit, for m\ge0, is F: in each fixed degree the truncation is eventually identical
to F. Apply [lem-pc-bounded-above-flat-tensor-acyclic] to (\tau_{\le m}F,P), and use [lem-pc-
module-filtered-colimits-tensor] to conclude that \operatorname{Tot}(F\otimes P) is acyclic.
4. For a degreewise short exact sequence 0\to A\to B\to C\to0 with flat terms in C, K-flatness
satisfies two out of three. Indeed [lem-weil-pbc-site-flat-quotient-tensor-ses] gives short
exact sequences after tensoring each degree with every F^p. Their finite direct sums are short
exact; the full direct sums along p+q=n are filtered colimits of these finite sums, so are short
exact by [lem-pc-module-filtered-colimits-tensor]. The resulting sequence of total tensor
complexes is therefore short exact. For acyclic F, the long exact sequence of [lem-weil-pbc-
complex-ses-homology-long-exact] shows that if two total tensors are acyclic, so is the third.
This is the required assertion by [def-pc-kflat-complex].
5. Module pullback commutes with sequential degreewise colimits. The natural bijections in [lem-
weil-pbc-ringed-topoi-module-adjunction] give, for every target module H,
\operatorname{Hom}(u^*(\varinjlim E_n),H)\cong\operatorname{Hom}(\varinjlim E_n,u_*H)
\cong\varprojlim\operatorname{Hom}(E_n,u_*H)\cong\varprojlim\operatorname{Hom}(u^*E_n,H).
This is exactly
the universal property of the colimit cocone (u^*E_n\to u^*(\varinjlim E_n)). The comparisons
commute with the differentials because they commute with all module morphisms. Also, pullback
preserves a short exact sequence 0\to F\to G\to H\to0 when H is flat. To check this without an
additional lemma, first apply the same adjunction to the ringed-topos map
(u,\mathrm{id}_{u^{-1}\mathcal O}): its module pullback is u^{-1}, so it preserves cokernels as
a left adjoint; it preserves kernels because these are finite limits of underlying sheaves and
u^{-1} preserves finite limits. Thus 0\to u^{-1}F\to u^{-1}G\to u^{-1}H\to0 is exact. By [lem-
weil-pbc-ringed-topos-flat-module-pullback] for this identity coefficient map, u^{-1}H is flat
over u^{-1}\mathcal O. Apply [lem-weil-pbc-site-flat-quotient-tensor-ses] with tensor factor
\mathcal O\prime to obtain 0\to u^*F\to u^*G\to u^*H\to0.
6. Use [lem-pc-flat-truncation-tower] for G=K to choose compatible epimorphic quasi-isomorphisms
E_n\to\tau_{\le n}K with each E_n bounded above and flat-term. Put L=\varinjlim_n E_n and let
q:L\to K be the induced map. Exact filtered colimits [lem-pc-module-filtered-colimits-tensor]
imply that q is termwise epimorphic and H^i(q) is an isomorphism for every i: take colimits of
the epimorphisms to the truncations and of their cohomology isomorphisms, using
\varinjlim_n\tau_{\le n}K=K. By steps 2 and 3, L is K-flat and flat-term.
7. Put M=\ker(q:L\to K). The sequence 0\to M\to L\to K\to0 is degreewise short exact. Since L^i
and K^i are flat, [lem-weil-pbc-site-flat-quotient-tensor-ses] gives flatness of M^i. Step 4
gives K-flatness of M, since L and K are K-flat and the quotient has flat terms. The long exact
sequence [lem-weil-pbc-complex-ses-homology-long-exact], together with the isomorphisms H^i(q)
of step 6, gives H^i(M)=0 for all i.
8. The complex u^*L is K-flat. Each u^*E_n remains bounded above because pullback takes zero to
zero (it is a left adjoint by [lem-weil-pbc-ringed-topoi-module-adjunction]); its terms are flat
by [lem-weil-pbc-ringed-topos-flat-module-pullback]. Step 3 gives K-flatness of each u^*E_n,
step 2 gives K-flatness of their colimit, and step 5 identifies that colimit with u^*L.
9. Prove the remaining acyclic case independently: let A be any acyclic K-flat flat-term complex
on the source site. By [lem-weil-pbc-site-acyclic-kflat-cycles-flat], Z^n(A) is flat. Hence
\tau_{\le n}A has flat terms: its degree-n term is Z^n(A), its lower terms are those of A, and
its higher terms are zero. Choose a compatible tower E_n\to\tau_{\le n}A by [lem-pc-flat-
truncation-tower], and define B_n as its degreewise kernel. Each B_n is bounded above, since
both E_n and the target are, and has flat terms by [lem-weil-pbc-site-flat-quotient-tensor-ses],
applied degreewise with flat middle and quotient.
10. For this tower put L_A=\varinjlim E_n and B=\varinjlim B_n. Exact filtered colimits [lem-pc-
module-filtered-colimits-tensor] give 0\to B\to L_A\to A\to0 and identify B with the kernel;
this uses the compatible maps B_n\to B_{n+1} induced by the commuting tower squares. By [lem-
weil-pbc-ringed-topos-flat-module-pullback], each u^*B_n is flat-term and still bounded above.
Steps 2, 3, and 5 imply u^*B=\varinjlim u^*B_n is K-flat. The same reasoning for E_n gives
K-flatness of u^*L_A. Apply the flat-quotient exactness argument of step 5 degreewise to the
sequence just obtained: its quotient A is flat-term. Thus 0\to u^*B\to u^*L_A\to u^*A\to0 is
short exact. Its quotient has flat terms by the flat-pullback lemma, so step 4 proves u^*A is
K-flat.
11. Apply the acyclic case proved in steps 9 and 10 to A=M of step 7. This gives K-flatness of
u^*M. Apply the flat-quotient exactness argument of step 5 degreewise to 0\to M\to L\to K\to0,
using flatness of K^i. The resulting short exact sequence 0\to u^*M\to u^*L\to u^*K\to0 has flat
terms in its quotient by step 1. Its first two complexes are K-flat by steps 10 and 8, so step 4
gives K-flatness of u^*K. Together with step 1 this proves both conclusions.
-/
theorem isKFlat_ringedToposPullback
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{w}} {S RI : Sheaf JD CommRingCat.{w}}
    (uInv : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (uPush : Sheaf JD (Type (w)) ⥤ Sheaf JC (Type (w)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      ringedSiteModules.{w} ((sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (a : M ⟶ N),
      uStar.map a = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    (P : CochainComplex (ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hP : P.IsKFlat) (hflat : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlat ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
      ∀ n : ℤ, IsFlatOnSite (J := JD) (R := S)
        (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n) := by
  sorry
end SheafOfModules
