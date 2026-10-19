## Worker report

The module `Sheaf.Paper.ConstructibleInternalHomContinuity` states
`AlgebraicGeometry.ProEtale.constructible_internalHom_continuity`, with one `sorry` and
no new definitions. It gives the equivalent cohomology-sheaf formulation explicitly
permitted by the node. Nothing is proved. The source statement and proof fields are unchanged.

Source reading: Bhatt--Scholze, *The pro-étale topology for schemes*, Lemmas 6.3.14,
6.8.12, and the support calculation in 6.7.13. I extracted the local PDF and read
6.3.14 (the triangulated devissage, open extension, locality and closed-support reduction)
and 6.8.12 (global direct sums with a common lower bound). The module identifies the
internal filtered-colimit assertion as the DAG's additional local devissage claim;
it does not misattribute that stronger formulation as a verbatim statement of the paper.
The declaration docstring gives all seven steps of the node's proof, naming its inputs,
including functorial truncation, the two-term scalar resolution, the uniform Hom bound,
the support-triangle argument and reconstruction from finitely many cohomology sheaves.

Hypotheses and clauses, in the order of the node:

- The prime is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Its canonical spectral norm
  is already used by the imported coefficient constructions. No arbitrary topology is assumed.
- The scheme is `(X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]`. This is the
  ascending chain condition on opens, equivalently the descending chain condition on
  closed subsets. There is no locally Noetherian, finite-dimensional, excellent,
  base-field or invertibility hypothesis on X.
- The condensed coefficient ring is the bundled ring object `Λ`; `_hΛ` says it is
  `Mon.mk (FiniteConstantModel.integralCoefficients l E)` or
  `Mon.mk (FiniteConstantModel.rationalCoefficients l E)`. Bundled equality includes
  the actual ring structure. `[IsCommMonObj Λ.X]` is the commutative-ring structure
  needed by the closed relative tensor and Hom, which both canonical choices possess.
  These are continuous functions into O_E and E, not discrete constant coefficient rings.
- `condensedRingObj Λ.X X` is exactly the existing `p_X^*Λ` with transported multiplication.
- `K : DerivedCategory (Mod ... (condensedRingObj Λ.X X))` is an object of the ordinary
  unbounded localization of cochain complexes of internal B-modules. No completion
  or finite-coefficient derived category is substituted.
- `_hK : constantModelBoundedConstructible Λ.X X K` is bounded cohomology plus
  finite-constant-model constructibility in every degree. It is the predicate of
  `sk-def-sfb-constructible`, not the upstream arbitrary-matrix local-presentation predicate.
- `{I : Type (u + 1)} [SmallCategory I] [IsFiltered I]` is a small filtered category
  in the coefficient/sheaf universe; filteredness includes nonemptiness. This admits
  arbitrary small categories, not just a sequential or poset diagram.
- `M : I ⥤ CochainComplex (Mod ... B) ℤ` is the diagram of actual cochain complexes;
  `(c : ℤ)` and `_hM : ∀ i r, r < c → IsZero ((M.obj i).X r)` are precisely its common
  termwise lower bound. There is no upper bound on M or bound on the number of its terms.
- `colimit.cocone M` is the chosen colimit of complexes, computed by termwise sheaf
  colimits. There is no extra colimit-existence hypothesis; existing instances supply it.
- In degree n, the actual functor applied to this cocone is
  `DerivedCategory.Q ⋙ (CondensedRing.derivedHom Λ.X X).obj (Opposite.op K) ⋙
  DerivedCategory.homologyFunctor _ n`. Its i-th leg is exactly
  `H^n(RHom(K,Q(colimit.ι M i)))`. Thus it uses the original colimit legs and the
  already defined right adjoint to derived relative tensor: evaluation defines the
  comparison, rather than an unspecified map or unspecified isomorphism.
- `∀ n : ℤ, Nonempty (IsColimit (...))` says the canonical map from the colimit of
  these cohomology sheaves to `H^n(RHom(K,Q(colimit M)))` is an isomorphism for EVERY n.
  This is exactly the equivalent formulation allowed in the node. Exact filtered
  sheaf colimits commute with cohomology of functorial representatives, so its
  source is the cohomology of their exact termwise colimit. Since only Q and the
  recorded derived functor appear, no resolution is chosen and the formulation is
  independent of quasi-isomorphic representatives. No conditions at all on the
  constructibility or completeness of the targets are present.

Dependency declarations read and reused:

- `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingObjOfUniverse`, is the recorded continuous-function
  condensed-ring interface; it is imported rather than copied.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj` and `isCommMonObj_condensedRingObj`, supply the actual monoidal
  inverse image and transported ring structure.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, is the recorded
  derived-category convention module; the category and localization here are the
  existing Mathlib `DerivedCategory` and `DerivedCategory.Q` it exports.
- `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
  `IsConstantModelConstructible` and `constantModelBoundedConstructible`, provide
  exactly the finite scalar-model notion. The source and docstrings were read.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`,
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom` and
  `derivedTensorHomAdjunction`, give the existing closed derived Hom over B.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.cocone`, `IsColimit`;
  `Mathlib.CategoryTheory.Filtered.Basic`: `CategoryTheory.IsFiltered`;
  `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `homologyFunctor`.
- The already landed `lem-sfb-finite-constant-model-two-term-free-resolution`, module
  `Sheaf.Paper.FiniteConstantModelResolution`, provides the canonical
  `FiniteConstantModel.integralCoefficients` and `rationalCoefficients`.
  This node was already a proof dependency and is added to stmt_deps solely because
  those coefficient definitions occur in the signature. No new node or dependency
  repair is needed. The stale sibling module `FiniteConstantModelTwoTermFreeResolution`
  is not used: the current recorded dependency is `FiniteConstantModelResolution`.

All currently recorded proof-dependency modules, including Mathlib matches and
closed Mathlib declarations, are imported non-publicly unless already public for
the signature. The 51-module pro-etale framework is read from the shared side source,
as required by `coord/pefw-upstream-framework.md`.

Edge cases checked before writing: the empty scheme; K=0; zero target diagrams;
a one-object filtered category; integral models with torsion O_E/(π^m); rational
rank zero and positive rank; arbitrary negative c; target complexes unbounded above;
Noetherian underlying spaces without Noetherian local rings. None is excluded.
An empty category cannot be filtered and is not an intended input. The n quantifier
ranges over all integers, including negative cohomological degrees. Source boundedness
is cohomological, and no termwise bound on its representative is imposed.

Searches actually run:

- `msearch.py ... leanfinder`: “Derived internal Hom from bounded constructible
  pro-etale integral adic sheaves preserves filtered colimits of uniformly bounded
  below complexes”. Eight hits on condensed AB axioms, colimits and monoidal structures;
  none state this coefficient-specific constructible-source continuity theorem.
- `msearch.py ... loogle`: `PreservesColimit, MonoidalClosed.internalHom`.
  Service answered zero hits and unknown identifier `PreservesColimit`; this is a
  query-resolution failure, not evidence that Mathlib lacks its preservation class.
  I subsequently read the existing `Limits.PreservesColimit` definition directly.
- `msearch.py ... leansearch`: “Derived internal Hom from constructible complexes
  commutes with filtered colimits of uniformly bounded below complexes”. Eight hits,
  including `HomologicalComplex.instHasFilteredColimitsOfSize`,
  `CategoryTheory.Limits.colimitLimitIso`, and AB5/preservation-of-homology results;
  none give the constructible-source internal Hom theorem.
- `msearch.py ... grep`: `(constructible|Constructible).*(RHom|derivedHom|colimit)|
  (RHom|derivedHom).*(constructible|Constructible)` over Mathlib: zero hits.
- Direct `rg` in the named upstream and shared Sheaf sources for constructible,
  derivedHom, internalHom, colimit and continuity found generic filtered coefficient
  passage (`DerivedInternalHomFilteredColimit`) which assumes precisely a continuity
  hypothesis, and perfect-Hom continuity on schemes. Neither states this theorem.
  The coefficient resolution helpers were found, read, and reused.
- `grep -rn 'lem-sfb-constructible-internal-hom-continuity'` in the specified upstream
  WeilConjectures tree: no match. Direct `rg` for the proposed declaration name in
  that tree, shared `lean/Sheaf` and `dag/lean_names_upstream.json`: no collision.

No statement dispute, statement correction, hollow definition, or extra mathematical
hypothesis was found. The resolved stage-1 repair note concerns the two extracted proof
lemmas; the Lean docstring uses both of those nodes and preserves the seven-step route.

## Second reading by Q25

This is the author's second reading under the direct-delivery arrangement, not a claim
of independent review; the maintainer supplies the independent reading. I re-opened the
node and the full Lean signature. I checked that NoetherianSpace is topological, that
both choices of Λ carry their actual bundled ring structures, that B is the recorded
inverse image, that bounded constructibility uses finite scalar models, and that the
common bound is termwise on every M_i rather than just separately boundedness.
I checked the resulting cocone has target H^n(RHom(K,Q(colimit M))) and the exact legs
obtained from each original coprojection. Nonempty IsColimit is equivalent to
invertibility of that canonical comparison, not merely existence of some isomorphism.
Every cohomological degree is covered, so the equivalent clause in the node is rendered
in full. I added the current coefficient-resolution node to stmt_deps when reusing its
helper definitions, and added explicit imports for closed Mathlib proof dependencies.
The first compiler run also identified the missing `CategoryTheory.Obj` scope needed to
expose the MonObj instance on the bundled coefficient ring; this scope was added.
No change to the mathematical statement was needed. Independent review is left to the
maintainer, as the dispatcher brief specifies.

Validation: the final module passed `scompile.py Q25
lem-sfb-constructible-internal-hom-continuity <module>` with no errors or warnings,
including the wrapper's sandbox check and library-path confirmation (24.2 seconds
for the confirmed library file). The signature was checked byte-for-byte against
`lean.statement`, every line is at most 100 characters, all variables/universes are
explicit, and the sole theorem proof is `sorry`.
