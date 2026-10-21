## Worker report

The module `Sheaf.RepresentationTheory.CommonIrreducibilityDetectingCover` states
`AlgebraicGeometry.Scheme.exists_common_irreducibility_detecting_cover` with its sole
proof `sorry`. The auxiliary `IrreducibilityDetectingModel` is a structure bundling
exactly the existential finite-field, representation, lattice and reduction-level
witnesses; it constructs no object by choice and has no postponed theorem or hidden proof.
No statement correction or dependency repair is needed.

Hypotheses and clauses, matched against the node:

- `X : Scheme.{u}`, `[ConnectedSpace X]`, `[IsNoetherian X]`, `[X.IsSeparated]`
  are the connected Noetherian separated base.
- `x : Spec (.of Ω) ⟶ X`, `[Field Ω]`, `[IsAlgClosed Ω]` are the geometric point.
- `l`, `[Fact l.Prime]` and `[∀ z : X, Invertible (l : X.residueField z)]`
  give the prime and its invertibility on the scheme.
- `K : Type (u+1)`, with `Algebra ℚ_[l] K` and `IsAlgClosure ℚ_[l] K`,
  is the fixed algebraic closure of the coefficient field. This is the recorded
  algebraic lisse category's coefficient universe, with no equality imposed on sites.
- `G : ProfiniteGrp.{u}`, its actions on finite-etale fibres and
  `IsFundamentalGroup (FiniteEtale.fiber x) G` present π₁ in the project's standard
  small model. `toAutContinuousMulEquiv` and the FLC comparison identify this
  with the fibre-functor automorphism group in the node; this is a presentation,
  not a restriction of the fundamental group.
- `r : ℕ`, `F : Fin r → LisseAlgebraicSheaf l X K` are the finite family,
  including `r = 0`. `hF j` says `¬ IsZero (F j)` and that every monomorphism
  from another lisse object has zero source or is an isomorphism. This is exactly
  nonzero with no nonzero proper lisse subsheaf, without presupposing global zero
  morphism instances for this localization category.
- Each `(M j).E : Padic.FiniteCoefficientFields l K` is a finite intermediate
  field of the fixed closure. `(M j).rank` supplies coordinates on V_j, and
  `(M j).ρ` is its linear automorphism action. The `continuous` field uses the
  recorded `Representation.IsContinuousCoefficient`, including finite dimension
  and joint continuity for the canonical spectral-norm/module topology.
- The existential `e` is a K-linear equivalence from `K ⊗_E V_j` to the actual
  algebraic fibre functor value. The recorded theorem
  `lisseAlgebraicFiberFunctor_obj` identifies that value with
  `lisseAlgebraicFiber l X K x (F j)`. The tensor flip identifies this source
  with the node's `V_j ⊗_E K`. Choosing coordinates excludes no finite-dimensional
  representation and specifies no basis of the original stalk.
- The equation after `e` is equivariance: on the tensor side it uses the recorded
  `Representation.coefficientScalarExtension`; on the stalk it conjugates
  `(d.eA.functor.obj (F j)).obj.ρ` by the recorded fibre comparison `d.τA`.
  The existential certificates `c` and `d` are the existing
  `GaloisLisseFiniteCorrespondence` and `GaloisLisseAdicCorrespondence`. Their
  evaluation clauses and rational/algebraic scalar-extension clauses identify
  this with the natural stalk action. They are supplied in the conclusion,
  not assumed as extra input, and their existence is exactly the proof dependency
  `galois_lisse_representations`.
- `(M j).lattice` is an actual submodule over the recorded coefficient integers
  in the coordinate E-vector space. Fields `finite`, `free`, `full`, `stable`
  assert finite generation, freeness, E-span equal to top and equality of every
  translate with the lattice. Thus these are the full stable finite free lattices,
  not abstract modules or unspecified actions.
- `uniformizer` and `generates` assert the span of its singleton is the recorded
  maximal ideal. `N` and `positive : 1 ≤ N` are the positive integer levels.
- `Q : Type u`, `Group Q`, `Finite Q`, `q : G →* Q`,
  `@Continuous G Q inferInstance ⊥ q` and `Function.Surjective q` supply the finite
  discrete quotient and continuous surjection.
- The pointwise kernel equality is `q g = 1 ↔ ∀ j v, v ∈ L_j →
  ∃ w ∈ L_j, ρ_j(g)v - v = uniformizer_j^N_j • w`. Since the lattice is stable,
  the right side says exactly that g acts identically on every
  `L_j / uniformizer_j^N_j L_j`. Equality with the intersection of the reduction
  kernels is therefore retained, with no arbitrary reduction homomorphism.
- `T : X.FiniteEtale` supplies the scheme and finite etale morphism `T.obj.hom`.
  `ConnectedSpace T.obj.left` is connectedness as a scheme. The fibre equivalence
  `e : (FiniteEtale.fiber x).obj T ≃ Q` and
  `e (g • t) = q g * e t` give exactly the required regular-action bijection.
  The surjectivity of the cover follows from its nonempty fibre (Q is a group).
- `∀ H : Subgroup G, q '' (H : Set G) = Set.univ → ∀ j, ...` includes arbitrary,
  possibly nonclosed H. The conclusion uses Mathlib's
  `Representation.IsIrreducible` for the scalar-extended action restricted by
  `H.subtype`, converted from linear automorphisms with
  `LinearEquiv.automorphismGroup.toLinearMapMonoidHom`. This includes nonzeroness
  and excludes all nonzero proper invariant K-subspaces.

Recorded dependency interfaces used:

- `Sheaf.Paper.LisseIntegralSmallCoefficients` publicly retains
  `Sheaf.Paper.LisseAdicSheaves`: `LisseAlgebraicSheaf`, its pair construction and
  `lisseAlgebraicFiber`; the small integral interface is not privately copied.
- `Sheaf.RepresentationTheory.LAdic`: `Representation.IsContinuousCoefficient`
  and `Representation.coefficientScalarExtension`, reexported by the
  correspondence-data module.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`: `flcFiber`, the geometric
  stalk functor on FLC; `WeilConjectures.AlgebraicGeometry.GaloisCategories`:
  `Scheme.FLC`; upstream `FundamentalGroup.FiniteEtale`: `FiniteEtale` and `fiber`.
- `Sheaf.Paper.GaloisLisseCorrespondenceData`: the existing finite and adic
  correspondence structures, including `eA`, `τA`, evaluation and scalar clauses.
- `Sheaf.Paper.LisseAdicFiberFunctors`: `lisseAlgebraicFiberFunctor` and its
  object-identification theorem.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`;
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly imports
  `CoefficientExtension`: `coefficientExtensionIntegers` and
  `coefficientExtensionMaximalIdeal`.

The four latter notion nodes were added to `stmt_deps` because the statement
explicitly uses their already-landed interfaces. No dependency node was edited.
All stated proof-dependency modules are imported, with proof-only imports non-public.
The docstring carries all eight steps of the node's proof, including the lattice
comparison, continuity of reduction, empty product and nonclosed subgroup cases.

Edge cases checked: r=0 has no model/stalk obligations, the empty intersection is
all of G, Q can be the trivial group and T=X. Rank zero cannot satisfy the
irreducibility conclusion for a nonempty family; no rank-positivity hypothesis was
added. Rank one works with an arbitrary stable full lattice. Distinct E_j are
allowed. For X a geometric point the group is trivial and the identity cover works.
There is no closedness or finite-index requirement on H. A geometric point excludes
an empty X; no additional nonemptiness assumption was added. The arbitrary
uniformizer has its generating condition; N=0 is correctly excluded.

Searches for existing statements/notions, 2026-10-21:

- msearch.py LeanFinder: "A common finite etale cover detects irreducibility of a
  finite family of lisse l-adic sheaves" returned eight general etale-site,
  irreducibility-of-schemes and open-cover results, none matching this theorem.
- msearch.py Loogle: `Representation.IsIrreducible, Submodule` returned zero hits.
- msearch.py LeanSearch: "A common finite quotient detects irreducibility of finitely
  many l-adic representations" returned eight results, including
  `Representation.IsIrreducible` and local-ring quotient finiteness, but no
  common quotient/cover assertion. The existing irreducibility definition is used.
- msearch.py grep: `detect.*irreducib|irreducib.*cover` in RepresentationTheory
  returned zero hits. Direct rg in Mathlib, WeilConjectures and Sheaf for the new
  declaration names found no collision. rg for common irreducibility/detecting-cover
  terminology and grep for this node id in WeilConjectures found no theorem match.
  Direct reads found the coefficient fields, lisse fibre, representation and
  correspondence definitions listed above, all reused rather than redefined.

## Second reading by Q55

This is the worker's final self-check; the maintainer performs the independent review.
Re-read the node and source proof against the final module. The coordinate choice
and tensor flip are only presentations. The original draft wrote the final
irreducibility clause out using all invariant subspaces; the final version uses
Mathlib `Representation.IsIrreducible` directly. Checked the exact kernel identity,
stability equality, positive levels, natural stalk conjugation, connected scheme
rather than categorical connectedness, and regular left action. No hypothesis or
clause was dropped. Every variable/universe is explicit with `autoImplicit false`.
