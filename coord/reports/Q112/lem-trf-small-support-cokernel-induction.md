## Worker report

Stage 2, Q112, 2026-10-23. The inherited ending was a stage-1 unchanged-item rejection.
The current node is an accepted stage-1 split, has no Lean record, and is a stage-2 queue
item. The 2026-10-22 handoff in coord/brief-stage2.md §0 explicitly authorizes recording
its statement. No repair note exists. I have preserved the accepted statement, proof,
dependencies and all other node fields; only `lean` changes.

The module `Sheaf.TraceFormula.SmallSupportCokernelInduction` states
`AlgebraicGeometry.exists_smallSupport_cokernel_induction` and the identity-base branch
`AlgebraicGeometry.exists_smallSupport_cokernel_zero`. Both proofs are `sorry`.
All other declarations assemble explicit quotients, tensors, localization maps or
conjunctions of the existing module/sheaf predicates. They belong to this same node,
are listed in `lean.declarations`, and introduce no independent mathematical notion.
Every declaration has its source and blueprint docstring. The main docstring carries
all seven proof steps, including the zero branch and the extension argument.

Clause-by-clause correspondence:

- A commutative local ring `(A,m)` is `[CommRing A] [IsLocalRing A]`, with
  `m = IsLocalRing.maximalIdeal A`. The algebra is `[CommRing B] [Algebra A B]`.
- The morphism is exactly `Spec.map (CommRingCat.ofHom (algebraMap A B))`.
  `[SmoothOfRelativeDimension n ...]` expresses smoothness and fibre dimension `n`;
  `n : ℕ` includes zero. This is the recorded notion of def-sbc-smooth-morphisms.
- `hgeom` quantifies over every prime `p` of `A` and every field `K` with a
  residue-field homomorphism `ι` compatible with the `A`-algebra structure. It requires
  `IsDomain (K ⊗[A] B)`. Nonzero and integral are both included in `IsDomain`.
  This is exactly extension of the fibre along `κ(p) → K`, by tensor associativity.
- `q : PrimeSpectrum B` supplies a prime ideal, and `hq` says its contraction is
  `IsLocalRing.closedPoint A`, whose ideal is `m`.
- `N,Q` are additive commutative groups with `B`-module structures and
  `[Module.Finite B N] [Module.Finite B Q]`. No finite presentation is assumed.
- `r : ℕ` includes rank zero; the finite free module is `Fin r → B`.
  The maps are `α : (Fin r → B) →ₗ[B] N` and `β : N →ₗ[B] Q`.
  `hinj`, `hexact` and `hsurj` are the three clauses of the stated short exact sequence.
- `hui` is injectivity of `(α.restrictScalars A).lTensor L` for every `A`-module `L`.
  The explicit `[Module A N] [IsScalarTower A B N]` records restriction of scalars;
  compatibility determines this action uniquely, so it is not a flatness assumption.
- `hflat` is `Module.Flat A (LocalizedModule q.asIdeal.primeCompl Q)` with its
  `A`-action explicitly obtained by `Module.compHom` along `algebraMap A B`.
- `smallSupportClosedFibre A B M` is the actual quotient
  `M ⧸ (m.map (algebraMap A B) • ⊤)`, namely `M/mM` as a `B`-module. The extended
  ideal has the same action as `m`, not a different closed-fibre construction.
- Mathlib's `Module.support B ...` means exactly nonzero localizations. Thus the
  left disjunct of `hdim` means `(Q/mQ)_q = 0`. In the right disjunct a witness of
  membership makes `q` a point of the support subtype; `topologicalKrullDimAt` on
  that subtype is its dimension at `q`, bounded strictly by `(n : WithBot ℕ∞)`.
- `hind` quantifies over every finite `B`-module `M`, with the precise localized
  `A`-flatness, nonzero closed-fibre localization (support membership), and strict
  support-dimension inequality in the node. Its conclusion is
  `smallSupportEtaleNeighborhood (A := A) (M := M) q`.
- In that conclusion, `C : CommAlgCat A` represents the affine scheme `T = Spec C`.
  The point is `t : PrimeSpectrum C`. `Etale (Spec.map ...)` is the existing étale
  notion; the closed-point equality and `IsIso (...residueFieldMap t)` specify the
  elementary pointed condition, including the given residue-field map.
- The actual local ring `A' = O_{T,t}` is represented by `Localization.AtPrime
  t.asIdeal`. This is the canonical affine local-ring model, identified with the
  structure-sheaf stalk by `StructureSheaf.IsLocalization.to_stalk`, not a chosen ring.
  Its `A`-algebra map is the composite `A → C → C_t`.
- `smallSupportBaseRing A B C t` is literally `B ⊗[A] C_t`, so it is `B'`.
  `B' ⊗[B] M` represents `M ⊗[A] A'` by the canonical associativity/symmetry map
  `(b ⊗ a') ⊗ m ↦ (b • m) ⊗ a'`, inverse `m ⊗ a' ↦ (1 ⊗ a') ⊗ m`.
  All actions are the existing tensor actions. There is no arbitrary module, map,
  isomorphism or `Nonempty` choice in these definitions.
- The induction conclusion names an actual open `U` of `Spec B'` and a point `q'`
  in it whose contraction to `B` is `q`. `smallSupportSheafGoodOpen` asserts precisely
  finite presentation of `tilde (ModuleCat.of B' (B' ⊗[B] M))` restricted to `U`,
  and `Scheme.Modules.IsFlatOver` along `U.ι ≫ Spec.map includeRight`.
- The main conclusion `smallSupportCokernelConclusion` names the same elementary
  affine neighbourhood and a prime `q'` contracting to `q`; its universal equality
  clause makes this the unique prime above `q`. It names `g : B'` with
  `g ∉ q'.asIdeal`, so the principal open contains the marked point.
- `smallSupportModuleGoodPrincipal` for `Q'` and, inside `smallSupportGoodPrincipal`,
  for `N'`, states their actual localizations
  `LocalizedModule.Away g ...` are finitely presented over `Localization.Away g`
  and flat over `A'`. The latter action is explicitly restricted along
  `Algebra.TensorProduct.includeRight`, as required; it is not flatness over `B'`.
- `smallSupportGoodPrincipal` additionally supplies finite presentation and relative
  flatness of the associated sheaf of `N'` on the actual principal open
  `PrimeSpectrum.basicOpen g`, exactly the final sheaf clause of the node.
  The conclusion for `Q'` contains its two module properties only.
- `smallSupportLocalizedFreeMap α g` has source exactly
  `Fin r → Localization.Away g` and target the actual localization of `N'`.
  It sends the standard basis vector `e_i` to `(1 ⊗ α(e_i))/1`; `Basis.constr`
  extends that specification linearly. `smallSupportLocalizedMap β g` is exactly
  tensor base change followed by `IsLocalizedModule.map`, sending fractions
  `z/g^j` to `β'(z)/g^j`. Its recorded linearity is over `B'`; the canonical map
  also commutes with the inverted powers, so the function is the indicated map of
  localized modules, not an existential replacement. Injectivity, exactness and
  surjectivity in the conclusion use these specific functions.
- `exists_smallSupport_cokernel_zero` keeps the common context of the node and
  replaces the support/induction assumptions by `hzero`. It quantifies `g : B`
  directly, uses the original maps localized by `smallSupportAwayFreeMap` and
  `smallSupportAwayMap`, and asserts `Subsingleton (LocalizedModule.Away g Q)`.
  Its finite-presentation, flatness, sheaf and exact-sequence clauses use `N_g,Q_g`
  themselves. Thus `A'=A` is built into its result and there is no `hind` parameter.

Universes are explicitly bound. The affine rings and modules have a common arbitrary
universe `u`; every finite module has such a representative because it is a quotient
of a finite free module. The test fields/modules live in `Type (max u v)`, never in a
universe independently smaller than the rings. In particular the identity residue-field
extension and the ordinary same-universe tensor tests are included. No extra equality
of site or coefficient universes is imposed.

Dependency interfaces read and used:

- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` and `SmoothOfRelativeDimension`.
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- def-kun-dimension: `WeilConjectures.Mathlib.Topology.KrullDimension`,
  `topologicalKrullDimAt` (infimum over open neighbourhoods).
- def-weil-etale-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Etale`.
- def-weil-residue-field: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`.
- def-weil-finitely-generated-module: `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`.
- def-sc-finitely-presented-module: `Mathlib.Algebra.Module.FinitePresentation`,
  `Module.FinitePresentation`.
- def-weil-pbc-flat-ring-map: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`,
  and the recorded `Module.Flat` definition, used for the module-flatness clauses.
- def-weil-pbc-module-localization: `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `LocalizedModule`, its `Away` form and `mkLinearMap`, and `IsLocalizedModule.map`.
- def-weil-pbc-module-tensor-product: its `mathlib_match`, `TensorProduct`,
  `LinearMap.lTensor`/`baseChange`, `Mathlib.LinearAlgebra.TensorProduct` modules.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `IsOpenImmersion`; the principal-open inclusions and `restrictFunctor` use it.
- pqf-def-coherent: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  `Scheme.Modules.IsQuasiCoherentFiniteType`. Its underlying existing
  `SheafOfModules.IsQuasicoherent`/`IsFiniteType` interfaces are inherited for `tilde`;
  no new quasi-coherence definition is made.
- def-weil-pbc-module-finite-type-presentation: the recorded Mathlib
  `SheafOfModules.IsFinitePresentation` (Sheaf.Quasicoherent), not module finiteness.
- def-pc-scheme-module-flat-over:
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`,
  `Scheme.Modules.IsFlatOver`, with its actual structural morphism.
- lem-weil-pbc-spec-module-tilde-sections: `Mathlib.AlgebraicGeometry.Modules.Tilde`,
  `tilde`, `tilde.toOpen`/`toStalk` and their canonical localization interfaces.

Proof-only imports include the stated localization-exactness, Nakayama, flat base-change,
flat localization, tensor right-exactness, affine finite-type/presentation and associated
sections modules. The finite-presentation kernel criterion is in the already public
`Mathlib.Algebra.Module.FinitePresentation` import. The pointed étale tower proof node
has no recorded Lean declaration or Mathlib match, so there is no module to import for
it; it remains named in the unchanged proof dependency list and in the proof docstring.
No proof import of the downstream finite-type-flat-neighbourhood theorem is added.

Edge cases checked before and after drafting:

- `r=0`: `Fin 0 → R` is the zero module and its basis map is the unique linear map;
  no nonempty rank, cancellation of rank or basis choice is imposed.
- `n=0`: a nonzero support at its point has dimension at least zero, so the strict
  inequality cannot hold; the vanishing branch remains available.
- `Q=0` and `Q_q=0` with `Q` nonzero elsewhere are both handled; the conclusion is
  local vanishing `Q_g=0`, not global vanishing of `Q`.
- For `A=k`, `B=k[x]`, `Q=B/(x)`, `q=(x-1)`, the zero branch can take `g=x`.
  For the nonzero branch, `q=(x)` and `n=1` have support dimension zero and already
  finitely presented flat `Q`; a split extension by `B^r` has the stated conclusion.
- Empty generating list permits `g=1`. `g=0` cannot avoid a prime, so the conclusion
  cannot accidentally certify an empty principal neighbourhood.
- The zero ring cannot supply the marked prime; no separate nontriviality hypothesis
  is inserted. Geometric-fibre nontriviality is already exactly part of `hgeom`.
- The identity base is present through the separate zero theorem, and the geometric
  field tests include the identity residue-field extension.

Searches on 2026-10-23 (all run using the prescribed msearch.py wrapper):

- LeanFinder: `small support induction universally injective finite free submodule
  cokernel flat etale neighborhood finitely presented`. Eight hits, including
  `Algebra.Etale.finitePresentation`, `Algebra.etaleLocus`,
  `Algebra.exists_etale_of_isEtaleAt`, `RingHom.Etale`; none is this conditional theorem.
- Loogle: `Module.FinitePresentation, Module.Flat`. Six hits, including
  `Module.Flat.projective_of_finitePresentation`, factorization results,
  `Module.exists_basis_of_span_of_flat`, `Module.isLocallyConstant_rankAtStalk`;
  none gives the stated support induction and pointed neighbourhood.
- Mathlib grep, RingTheory: `support.*induct|cokernel.*neighbo|universally.*injective`:
  zero hits. Direct source reading found the existing `Module.support`, defined by
  nonzero localization, which is used rather than redefined.
- LeanSearch: `small support induction finite cokernel universally injective free
  submodule flat etale neighborhood`. Eight hits, flat/free Finsupp results and
  flatness induction/criterion declarations; no matching theorem.
- Project `rg` for `small.support|cokernel.induction|finite-type-flat-at-point` found
  the parent finite-type-flat-neighbourhood theorem and unrelated small-support
  category-theory lemmas. The parent has no smaller-support conditional hypothesis
  and does not state this exact-sequence/principal-open/identity-base conclusion.
- `grep -rn 'lem-trf-small-support-cokernel-induction' lean/WeilConjectures`: no hits.
  Both roots were searched for all newly introduced helper names; no declaration
  clashes or existing copies were found.

No new nodes, dependency record repairs, statement corrections or disputed statements.

## Second reading by Q112

This is the dispatched author's separate self-reading, not a claim to an independent
second agent; the dispatch forbids starting other agents and the maintainer independently
reviews the delivery. I reopened the accepted node and the full module and compared the
hypotheses and conclusions above. I checked particularly the closed-fibre quotient, local
dimension on the support subtype rather than local-ring dimension, the induced residue
map, the actual local-ring model and both tensor actions, uniqueness of the prime, and
the exact canonical arrows. The first reading exposed two missing explicit `A := A`
arguments in the packaged predicates; these were fixed. The next reading replaced the
zero branch's canonically isomorphic `B ⊗[B] N` sequence by the sequence on `N_g` itself
and retained its common hypotheses verbatim, with no induction hypothesis. No node text
or accepted split changed. Every postponed theorem matches this node; helper data contain
no `sorry` and no arbitrary chosen morphism or object.

## Validation

The prescribed scompile.py compiled the module in sandbox and library module mode
with no warnings or errors. The first deliver2.py dry run passed preflight and compile.
A final clause check removed the redundant associated-sheaf conclusion for Q, retaining
exactly its module properties and the stated associated-sheaf conclusion for N; the
complete compiler and delivery checks are repeated on that final revision.
The final file starts with `module`, exports statement dependencies with `public import`,
and uses plain `import` for proof-only dependencies. All universes and variables are bound.
The full deliver2.py dry run and delivery are run after this report is written.
