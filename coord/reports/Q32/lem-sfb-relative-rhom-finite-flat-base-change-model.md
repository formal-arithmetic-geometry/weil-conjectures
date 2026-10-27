## Worker report

Item: lem-sfb-relative-rhom-finite-flat-base-change-model. Source read in full:
`literature/stacks-project/more-algebra.tex`, lemma-compute-RHom-relatively-perfect,
Tag 0E1U, including its last finite-presentation paragraph and proof. The statement
is unchanged. One module belongs to the item:
`Sheaf.Algebra.Homology.RelativeRhomFiniteFlatBaseChangeModel`.
Its only postponed theorem is
`CochainComplex.relativeRhom_finiteFlat_baseChange_model`; its proof is `sorry`.
Every helper definition has actual data. There are no new nodes or dependency repairs.

Hypotheses and clauses, in the order of the mathematical statement:

1. Commutative rings and the specified homomorphism are `R S : Type u`,
   `[CommRing R] [CommRing S] [Algebra R S]`. Algebra structure is the usual bundled
   presentation of an arbitrary ring map. Flatness is exactly
   `hflat : RingHom.Flat (algebraMap R S)`; finite presentation is
   `[Algebra.FinitePresentation R S]`. There is no Noetherian assumption.
2. Ordinary derived objects are `K L : DerivedCategory (ModuleCat.{u} S)`.
   The project provides the canonical small-Hom localization and its monoidal
   structure for this module category. `hK` and `hL` use the recorded
   `DerivedCategory.IsPseudoCoherent`, without a private replacement.
3. `hTor` quantifies `∃ a b : ℤ, a ≤ b` and EVERY `N : ModuleCat.{u} R` and
   `i : ℤ` outside that interval. The cohomology object of the derived tensor of
   restricted L with `N[0]` is `IsZero`. Tensor is the existing derived tensor,
   not the ordinary tensor of an arbitrary representative. The test module's
   universe equals the ring's universe, so this quantification is not vacuous.
4. `RelativeFiniteFlatHomModel` packages precisely the allowed choices P,F.
   `upper` is bounded-above P; `free` is `Module.Free S` AND `Module.Finite S`
   in every degree. `bounded` says F vanishes outside some finite interval;
   `flat` is `Module.Flat R` after the actual restriction-of-scalars functor;
   `fp` is `Module.FinitePresentation S`. The latter is Mathlib's finite
   generators plus finitely generated kernel definition, equivalent to the
   displayed finite free presentation. The first existential of the theorem
   supplies isomorphisms `Q(P) ≅ K`, `Q(F) ≅ L` for such a model.
5. The universal quantifier over `RelativeFiniteFlatHomModels R S` means EVERY
   allowed P,F, not just the particular model constructed for K,L. E is exactly
   the dependency's `moduleHomComplex M.P M.F`. Its differential is already
   Mathlib's `HomComplex.δ_hom`, i.e. d_F h - (-1)^n h d_P. No second differential
   or Hom complex is defined here. The first universal conjunction supplies
   a lower bound, R-flatness, and S-finite presentation of every E term.
   The normalized linear equivalence `σ` identifies E^n with the direct sum
   over all integer i of `P^i →ₗ[S] F^(i+n)`, and its component formula says
   that this is the actual family of homogeneous components. Finite support
   follows from the given bounds, including for negative n.
6. `H`, `eH`, and the NATURAL isomorphism `α` identify Q(E) with the recorded
   ordinary-module RHom. The model category is `InducedCategory` of the pair
   `(op (Q P), Q F)`, so its arrows are arbitrary DERIVED source and target
   morphisms. It includes changes of representatives. The evaluation family
   `ev` is fixed on every pure homogeneous tensor by its signed evaluation
   formula. The equation involving `α`, `eH` and `ihom.ev` normalizes this
   derived representative by evaluation, rather than allowing an arbitrary
   isomorphism of the two objects. The sign (-1)^(p*n) is the established
   bridge between the project's unsigned Hom differential and its tensor
   ordering P tensor Hom; see the existing projective evaluation model.
7. Every T has only `[CommRing T] [Algebra R T]`. `relativeHomCoefficientMap`
   is precisely S -> S tensor_R T, the include-left homomorphism.
   `relativeHomExtend` abbreviates the EXISTING ordinary termwise scalar
   extension. The two `IsIso (relativeHomScalarCounit ... M.P/F)` clauses
   assert that the canonical derived-to-ordinary comparisons are invertible,
   and therefore the ordinary extended P,F represent K_T,L_T. The existing
   counit is natural on all chain maps. There is no assumption that T/R is flat.
8. `χ` is a family of CHAIN ISOMORPHISMS, not merely quasi-isomorphisms or an
   unspecified map. Its formula on c tensor h and d tensor x is
   `(c*d) tensor h(x)`. Taking c=1 tensor t and d=1 tensor u gives exactly
   `(h tensor t)(p tensor u) = h(p) tensor tu` after balancing. The `ω` clause
   explicitly provides that natural ordinary balancing isomorphism:
   t tensor x maps to (1 tensor t) tensor x. Thus the left side is ordinary
   termwise tensor over R, although the typed S_T-module presentation is
   ordinary extension along S -> S_T. Neither ordinary tensor is silently
   replaced by derived tensor on E, which need not be K-flat.
9. `HT`, `eT`, `β`, and `γ` state Q(E_T) ≅ RHom(K_T,L_T). The equation
   `eT.hom ≫ Q(χ.hom) ≫ γ.hom = β.hom` says this derived comparison is
   represented by the specified chain isomorphism. The equation for `γ`
   with the two scalar counits and evaluation fixes the target derived
   identification by the SAME normalized evaluation. Thus neither α nor γ
   is an unrelated isomorphism introduced merely to obtain naturality.
10. `θ` is the additive bijection H^0(E) -> Hom_D(S)(Q P,Q F), fixed on
    every cycle coming from a chain map by `θ(π z)=Q.map f`.
    The equation `χ(1 tensor h)=h.map (extendScalars ...)` in every degree
    identifies tensoring a zero cocycle with the ordinary extended chain map.
    Together with the explicitly written derived scalar-counit naturality
    square, this says that the class goes to derived scalar extension of
    that morphism. It covers boundaries too: a chain isomorphism descends
    to homology, and tensoring preserves the chain homotopy equation.
11. The chain-map naturality clause fixes the action of H and HT on chain
    maps by the actual pre/postcomposition formula for a Hom cochain.
    These are functors on the category with ALL derived morphisms, and α,β
    are natural isomorphisms there. A derived source morphism has a chain
    representative because P is bounded above finite free. A target
    morphism has the bounded-flat roof refinement of proof step 8 of the
    node; its left leg remains invertible after any extension. Functoriality
    therefore determines the action on these roofs as well. This is why the
    statement's naturality covers derived morphisms and model choices.
12. Iteration quantifies arbitrary R-algebra maps `v : T →ₐ[R] U`, hence
    every composable ring extension R -> T -> U with its composite R-action.
    `τ` is the tensor associator, characterized on the unit pure tensors.
    `ξ` is itself a chain isomorphism for the second Hom extension, with its
    component formula transported through τ on P and F. The final equality
    says that extending χ_T and then using ξ equals χ_U after reassociation.
    The T=R comparison, after S tensor_R R ≅ S and the tensor unitors, is
    the identity: its displayed c*d evaluation formula is h(x). This also
    fixes the identity case, rather than imposing a convention that applies
    only to nonidentity extensions. Natural isomorphisms preserve identity
    arrows and the iterated equations preserve composites.

Dependency declarations used (source signatures and docstrings read):

- def-weil-pbc-flat-ring-map: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`,
  with `Module.Flat` for individual terms.
- def-weil-pbc-finitely-presented-algebra:
  `Mathlib.RingTheory.FinitePresentation`, `Algebra.FinitePresentation`.
- def-weil-abstract-derived-category:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `DerivedCategory.Q`; imported publicly through the recorded ordinary interfaces.
- lem-pur-derived-change-of-rings:
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`,
  `ModuleCat.ordinaryDerivedExtendScalars`, `ordinaryDerivedChangeOfRings`,
  `OrdinaryDerivedChangeOfRings.counit`.
- def-pur-derived-internal-hom:
  `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`,
  `CategoryTheory.ordinaryModuleDerivedInternalHom`.
- def-pc-ring-pseudo-coherent-complex:
  `WeilConjectures.RingTheory.RingPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`.
- def-sc-module-total-hom-complex:
  `WeilConjectures.Algebra.Homology.ModuleHomComplex`,
  `CochainComplex.moduleHomComplex` and Mathlib's `HomComplex.Cochain`.
  This already recorded proof dependency is publicly imported because the
  signature uses it. The item's stmt_deps are unchanged.

All currently stated proof dependencies are imported (plain import when only used
by the proof plan): BoundedFlatKFlat, FlatOpcyclesTorCriterion,
MixedTensorKFlatQuasiIso, SingletonSiteModuleComparison,
AffineProjectiveComplexDerivedHom, ProjectiveHomEvaluationModel and Mathlib's
DerivedCategory.KProjective. The two proof dependencies
lem-trf-half-bounded-hom-scalar-isomorphism and
lem-sfb-flat-algebra-derived-module-tensor-exchange have no Lean record or
Mathlib match in the read clone, so have no module to import. They are not needed
to TYPE this statement; the proof docstring retains their intended uses.

Searches (full outputs/log digests in the sandbox's searches.jsonl):

- msearch leanfinder, query "For pseudo coherent complexes over a flat finitely
  presented algebra with relatively finite Tor amplitude, Hom of finite free
  and bounded flat representatives commutes with arbitrary base change": eight
  unrelated algebra/scheme flat-base-change results, no exact statement.
- msearch loogle, `Module.Flat, Module.FinitePresentation,
  CochainComplex.moduleHomComplex`: no hits; the project-only Hom name is
  unknown to the service.
- msearch grep, `pseudo.?coherent|relatively.?perfect|RHom`,
  Mathlib/Algebra/Homology: 25 generic bifunctor/monoidal results, no theorem.
- msearch leansearch, "Hom complex of a bounded above finite free complex
  and bounded flat complex commutes with arbitrary extension of scalars":
  HomComplex, extendScalars and HomologicalComplex.Hom.mk among eight hits;
  no finite-flat model theorem.
- rg in both lean/WeilConjectures and lean/Sheaf for the item id,
  RelativeRHom, relativeRHom, finiteFlat, scalar/Hom-complex and model names:
  found the shared Hom complex, projective evaluation theorem and the
  AlgebraicDiagonalGeneratorBaseChange consumer, no duplicate theorem.
- rg of dag/lean_names_upstream.json and both source trees for all newly
  named model/interface helpers: no existing name. `blueprint_refs.py search
  Hom complex` found related blueprint nodes, not this packaged interface.
  Helpers only collect the SAME notion's representatives and normalized
  comparison types; no independent mathematical notion is defined here.

Edge cases checked mathematically: zero rings S or T, zero K or L, all-zero
representatives (free of rank zero and empty direct sums), singleton Tor
interval a=b, negative degrees and arbitrary support bounds, T=R, v=id,
nonflat extension Z -> F_p, and R=S=Z with K=Z and L=Z/p. In the last case a
finite free resolution computes the extra derived Tor summand after tensoring
with F_p; the statement uses ordinary tensor of F and E with their flat terms,
so it retains that summand. E is bounded below but is never assumed K-flat.
No STATEMENT-DISPUTED flag, mathematical correction, or dependency defect found.

Validation: the delivered module is checked by scompile.py in module mode, both
as sandbox source and under its final library module name. Only the single
stage-2 theorem has a postponed proof. The delivery dry run is recorded below.

Dry run: `deliver2.py Q32 lem-sfb-relative-rhom-finite-flat-base-change-model
--no-push` printed `OK (dry run): commit bcd329fd217 passes the preflight and
compiles; nothing pushed`. The node's recorded signature was checked byte for
byte against the theorem signature. All Lean lines are at most 100 characters;
`autoImplicit false` is enabled and the only `sorry` is the main theorem proof.
The wrapper supplies the administrative second-reading heading recording that
independent mathematical review belongs to the maintainer; no worker second
reading is claimed here.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
