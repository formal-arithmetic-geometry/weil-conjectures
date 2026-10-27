module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
import Mathlib.Algebra.Module.Projective
import Sheaf.RingTheory.LocalUniversalInjectiveResidue
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.PairHenselization
import WeilConjectures.RingTheory.PairHenselizationFlatQuotients
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent
import Sheaf.RingTheory.FlatnessFaithfullyFlatExtension

/-! # Finite sources with an injective closed-fibre map into a flat module

Source: Stacks Project, More on Flatness, Tag 0AT4,
`lemma-upstairs-finite-type-injective-into-flat-mod-m`.
(blueprint: lem-sfb-finite-source-fibre-injective-flat-target).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w x y

namespace Module

/-- A finite source over a local essentially finite type algebra is base-flat and
finitely presented if its closed-fibre map into a base-flat module is injective.
The closed-fibre map below is literally a map between the quotients by the base
maximal ideal: the canonical tensor/quotient equivalences send the class of n
through n tensor 1 to the class of f n. No finiteness is imposed on the target.

Source: Stacks Project, More on Flatness, Tag 0AT4, using Tags 0AT3 and 0AT2.
(blueprint: lem-sfb-finite-source-fibre-injective-flat-target).

Proof (the nine steps of the DAG node):
1. First prove the following auxiliary implication for any henselian local A, local essentially
finite type A-algebra C, finite C-module P and A-linear v:P\to T with T flat and \bar v injective:
if P is already A-flat, then v is universally injective. Use the free-colimit node to write
P=\varinjlim F_d. Tensor commutes with colimits, so P/\mathfrak mP=\varinjlim(F_d/\mathfrak mF_d).
Each map into this last colimit is injective: an element mapping to zero vanishes at a later stage
by the elementwise criterion, and the transition map is injective. Thus every F_d\to T is
residue-injective. Free modules are projective, so the local projective-source criterion makes
every F_d\to T universally injective. For any A-module Q, write an element of P\otimes_AQ at a
stage F_d\otimes_AQ. If its image in T\otimes_AQ vanishes, injectivity at that stage kills the
representative. This proves the auxiliary implication, with no linearity of v over C needed. Uses:
lem-sfb-henselian-flat-finite-module-residue-free-colimit,
lem-weil-pbc-tensor-commutes-with-colimits, lem-weil-pbc-filtered-colimit-modules-elementwise,
lem-weil-pbc-free-module-projective, lem-trf-local-universal-injective-residue.
2. Still with A henselian, prove the assertion when A\to C is essentially of finite presentation
and P is finitely presented over C; allow the map v:P\to T to be only A-linear. Choose the
finitely generated ideal I\subseteq\mathfrak m_A from the quotient-flattening node. It gives P/IP
flat over A/I. The ring A/I is henselian: a finite A/I-algebra is finite over A, and the
idempotent-lifting criterion for A applies with the same residue quotient. The map A/I\to C/IC is
local and essentially of finite type, and P/IP is finite over C/IC, as follows by reducing
generators and the algebra presentation. Moreover T/IT is flat over A/I: tensoring an injection of
A/I-modules with it is the same as tensoring with T over A. The closed-fibre map of v\bmod I is
the original injective \bar v. Step 1 therefore makes P/IP\to T/IT universally injective over A/I.
Uses: lem-sfb-henselian-fp-module-quotient-flattening-ideal, def-weil-pbc-henselian-terminology,
def-weil-pbc-flat-ring-map.
3. Tensor 0\to I/I^2\to A/I^2\to A/I\to0 over A with P and with T. Right exactness gives the
bottom row P\otimes_A I/I^2\to P/I^2P\to P/IP\to0; flatness of T makes the corresponding top row
start with zero. In the commutative diagram induced by v, the left vertical map is injective: it
identifies with (P/IP)\otimes_{A/I}I/I^2\to(T/IT)\otimes_{A/I}I/I^2, which is injective by step 2.
If an element in the lower left maps to zero in the lower middle, its image upstairs maps to zero,
hence is zero by upper-row injectivity, and hence the original element is zero. Thus the lower
left multiplication map is injective. Apply the nilpotent-ideal flatness criterion to R=A/I^2, its
square-zero ideal I/I^2 and the module P/I^2P. The reduced module is P/IP, already flat, so P/I^2P
is flat over A/I^2. Uses: lem-weil-pbc-tensor-right-exact, lem-weil-pbc-flat-tensor-exact,
lem-sfb-nilpotent-ideal-module-flatness.
4. By the equivalence defining I, now with J=I^2, step 3 implies I\subseteq I^2. Hence
I=I^2\subseteq\mathfrak m_AI, so I=\mathfrak m_AI. Nakayama for the finite A-module I gives I=0.
The same equivalence with J=0 now proves P flat over A. Step 1 proves v universally injective.
Finite presentation over C was a hypothesis of this case. Uses:
lem-sfb-henselian-fp-module-quotient-flattening-ideal, lem-weil-pbc-nakayama-jacobson.
5. Remove the presentation hypotheses in the henselian case. Choose the local surjection
C=A[x_1,\ldots,x_r]_{\mathfrak q}\twoheadrightarrow B furnished by the polynomial-cover node and
regard N as a finite C-module. Put k=A/\mathfrak m_A. The field k is Noetherian (its only ideals
are zero and the unit ideal); finite-type Noetherianity and localization Noetherianity show
C/\mathfrak m_AC is Noetherian. Write N=C^s/K. The image \bar K of K in (C/\mathfrak m_AC)^s is
finitely generated by the submodule finiteness node. Lift generators to k_1,\ldots,k_t\in K and
put K'=\sum Ck_j, P=C^s/K'. Then P is finitely presented over C, and the surjection p:P\to N is an
isomorphism modulo \mathfrak m_A, since both residue presentations have relation submodule \bar K.
Uses: lem-trf-local-essentially-finite-type-polynomial-cover,
lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian,
lem-weil-pbc-noetherian-submodule-finite.
6. Apply steps 2–4 to the A-linear composite P\xrightarrow{p}N\xrightarrow{u}M. Its residue map is
injective by step 5 and the hypothesis, and A\to C is essentially of finite presentation. The
composite is universally injective, in particular injective for Q=A, so the surjection p is
injective and is an isomorphism. Thus N is flat over A and u universally injective. For finite
presentation over B, tensor the finite presentation C^t\to C^s\to N\to0 with B. Right exactness
gives B^t\to B^s\to B\otimes_CN\to0, and B\otimes_CN\cong N via b\otimes x\mapsto bx since C\to B
is surjective. This proves all three assertions in the henselian case, even for an A-linear map.
Uses: lem-weil-pbc-tensor-right-exact.
7. For general A, take the henselization H of the pair (A,\mathfrak m_A). The pair-henselization
and comparison nodes give a henselian local ring H with maximal ideal \mathfrak m_AH and residue
field k. The flat-quotients node says A\to H is flat. Set D=B\otimes_AH. The ideal \mathfrak
n=\mathfrak m_BD+\mathfrak m_HD is maximal because D/\mathfrak n\cong B/\mathfrak m_B, and put
B'=D_{\mathfrak n}. The maps B\to B' and H\to B' are local. The latter is essentially of finite
type, by extending the finite algebra generators and then localizing. The map B\to D is flat: for
a B-linear injection, its tensor with D identifies with its tensor over A with H. Localization is
flat, and composing these tensor injections shows B\to B' flat. It is faithfully flat by the flat
local homomorphism node. Uses: lem-weil-pbc-pair-henselization,
lem-per-local-pair-henselization-comparison, lem-weil-pbc-henselization-flat-quotients,
lem-weil-pbc-localization-flat, lem-weil-pbc-flat-local-hom-faithfully-flat,
def-weil-pbc-flat-ring-map.
8. Put N'=N\otimes_BB', M'=M\otimes_BB' and u'=u\otimes_B1. The chosen generators show N' finite
over B'. Identify M' with the localization at \mathfrak n of M\otimes_AH. The latter is H-flat,
since its tensor with any injection of H-modules identifies with the tensor over A with M;
localization preserves this flatness. Modulo \mathfrak m_H the ring B' identifies with B/\mathfrak
m_AB: after quotienting D by \mathfrak m_H, its localization is at the maximal ideal of the
already local ring B/\mathfrak m_AB, hence changes nothing. Accordingly \bar u' identifies with
\bar u and is injective. Steps 1–6 applied to H\to B' therefore give N' flat over H, finitely
presented over B', and u' universally injective over H. Uses:
lem-pc-affine-flat-module-localization-preserves-flatness, def-weil-pbc-flat-ring-map.
9. Finite presentation of N over B descends from that of N' over B' by the finite-presentation
descent node. Also N' is A-flat: tensor an A-linear injection first with flat H and then with the
H-flat module N'. The faithfully-flat-extension flatness node for A\to B\to B' now gives N flat
over A. Finally, for any A-module Q, identify the base change along B\to B' of u\otimes_A1_Q with
u'\otimes_H1_{H\otimes_AQ} using associativity, x\otimes b'\otimes q\mapsto(x\otimes
b')\otimes(1\otimes q). It is injective by step 8. Faithful flatness reflects exactness of the
two-term complex 0\to N\otimes_AQ\to M\otimes_AQ, so u\otimes_A1_Q is injective. This is the
required universal injectivity for every Q. Uses:
lem-trf-finite-presentation-module-descent-flat-local, lem-trf-flatness-faithfully-flat-extension,
def-weil-pbc-faithfully-flat-ring-map.
-/
theorem flat_finitePresentation_universallyInjective_of_closedFiber_injective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    {N : Type w} {M : Type x} [AddCommGroup N] [AddCommGroup M]
    [Module B N] [Module A N] [IsScalarTower A B N]
    [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B N] [Module.Flat A M] (f : N →ₗ[B] M)
    (hres : Function.Injective
      ((TensorProduct.tensorQuotEquivQuotSMul M (IsLocalRing.maximalIdeal A)).toLinearMap ∘ₗ
        (f.restrictScalars A).rTensor (A ⧸ IsLocalRing.maximalIdeal A) ∘ₗ
        (TensorProduct.tensorQuotEquivQuotSMul N (IsLocalRing.maximalIdeal A)).symm.toLinearMap)) :
    Module.Flat A N ∧ Module.FinitePresentation B N ∧
      ∀ (Q : Type (max u v w x y)) [AddCommGroup Q] [Module A Q],
        Function.Injective ((f.restrictScalars A).rTensor Q) := by
  sorry

end Module
