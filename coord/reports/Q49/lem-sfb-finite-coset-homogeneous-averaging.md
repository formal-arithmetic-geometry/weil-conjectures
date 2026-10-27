## Worker report

The module `Sheaf.RepresentationTheory.FiniteCosetHomogeneousAveraging` states the entire
node through three theorems, with `sorry` proofs. Its two supporting definitions contain
actual canonical data. This repaired delivery adds a definition-only attachment for
the existing coordinate structure. No statement correction or disputed statement is needed.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
As the node explicitly records, the arithmetic finite-coset argument is an agent-written
auxiliary expansion, not a claim printed verbatim in this blueprint paragraph. All nine
accepted proof steps are transcribed in the theorem docstrings at their relevant places.

Hypotheses and clauses, matched against the node:

- A topological field E is `[Field E] [TopologicalSpace E]
  [IsTopologicalDivisionRing E]`. The dependency `def-weil-field` is the Mathlib leaf
  `Field`, read with its docstring in `Mathlib/Algebra/Field/Defs.lean`.
- A topological group is `[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`.
  Only transversal existence and the main averaging theorem use `[CompactSpace G]`;
  the retraction identities hold without compactness. A subgroup H is `Subgroup G`
  with `IsOpen (H : Set G)`; its topology is Mathlib's induced subgroup topology.
- A finite normalized right transversal is `S : Finset G`, `1 ∈ S`, and
  `Subgroup.IsComplement (H : Set G) (S : Set G)`. Mathlib defines this as bijectivity
  of multiplication H × S → G. The first theorem asserts its existence together with
  `S.card = H.index`. Thus these are right cosets Hs, not left cosets sH.
- `finiteCosetRetraction` is the actual expression
  `x * (hS.toRightFun x : G)⁻¹`, bundled in H using Mathlib's existing membership
  theorem. The second theorem asserts `Continuous r`, `x = r(x) s(x)`, and uniqueness
  among all maps giving such decompositions. It separately asserts `r(hx)=h r(x)`
  and `r|H=id`. The transversal is arbitrary, not only the one in the existence theorem.
- `finiteCosetArgument H S hS s x` is exactly `s⁻¹ * (r(s*x) : G)`.
  The second theorem asserts continuity for every `s : S`. For every a it supplies
  `π : Equiv.Perm S` with `s*a*(π s)⁻¹ ∈ H` and `a_s(a*x)=a*a_(π s)(x)`.
  The membership condition says exactly Hsa=H(π s); the transversal makes this
  representative unique. Being an equivalence states permutation, including its inverse.
- Topological vector spaces V and W have `AddCommGroup`, `Module E`,
  `TopologicalSpace`, `IsTopologicalAddGroup`, and `ContinuousSMul E`.
  Actions `ρ : G →* V ≃ₗ[E] V` and `σ : G →* W ≃ₗ[E] W` are linear group actions;
  their explicitly quantified continuity is on `G × V` and `G × W`, respectively.
- The existing `ContinuousCohomology.JointContinuousCochainCoordinates` in
  `Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates` supplies B.
  I read its full structure and both theorem signatures and docstrings. Its `bEval`,
  `bInjective`, `bRange` identify B^n with *all* jointly continuous homogeneous
  equivariant functions, with pointwise linear operations. Its `delta` is exactly
  the sum over `Fin (n+2)` with sign `(-1:E)^i.val` and deletion `i.succAbove`;
  `bNegative` asserts zero in every negative integer degree. Consequently a morphism
  `BH ⟶ B` is precisely an E-linear cochain map of the requested complexes.
  `DH` uses the restricted action `ρ.comp H.subtype`. B, BH, and the auxiliary C, CH
  are arbitrary realizations of this exact interface; its landed existence theorem
  gives such realizations for every coefficient space. No assumption about a chosen
  arbitrary map substitutes for a canonical construction.
- The main theorem asserts `∃ (T : BH ⟶ B) (R : B ⟶ BH)` and its first evaluation
  identity is precisely the specified sum of `ρ s⁻¹ (f(r(s*x_i)))`.
  Its second identity specifies R by restriction along H → G.
  Its third identity evaluates `R ≫ T`, which is T after R in Mathlib convention,
  as the sum of `F(a_s(x_i))`. The cochain-morphism types state differential
  compatibility in every integer degree, including the extension by zero.
- T is quantified before W, σ, their complexes, and b. With the same S, hS and
  `finiteCosetRetraction`, the theorem gives TW satisfying the identical averaging
  formula, before quantifying b. For every linear `b : V →ₗ[E] W` with continuity
  and `b(ρ a z)=σ a (b z)`, the maps bG and bH are specified by postcomposition
  evaluation identities. The final equality `bH ≫ TW = T ≫ bG` is exactly
  `T_W b_* = b_* T_V`. Evaluation injectivity and zero negative terms make all
  these maps unique, so this states simultaneous naturality, rather than allowing
  different unrelated transfers for different b. V and W have independent universes.
- No normality, coefficient completeness, local compactness, discrete topology,
  separation, characteristic-zero, or invertible-index hypotheses occur. The extra
  `HasDerivedCategory` parameter is inherited from the existing coordinate interface;
  Mathlib supplies `HasDerivedCategory.standard`, so it imposes no mathematical
  restriction. The ambient ModuleCat universe is independent of both carrier universes;
  one may choose a common maximum and the coordinate existence theorem provides it.

Dependency declarations used: `Field` (Mathlib.Algebra.Field.Defs) and
`ContinuousCohomology.JointContinuousCochainCoordinates`, attached by the new definition
node `def-sfb-joint-continuous-cochain-coordinates` to its existing module
`Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates`. The item's
`stmt_deps` is now exactly the field node and this definition node. D/DH/DW/DHW are
quantified coordinate data, not applications of the existence theorem. The existence
and naturality theorems were read for context but are not statement dependencies.
The new definition depends only on the field and abstract-derived-category definition
nodes. The public import stays the existing module because it exports the structure.

Mathlib notions reused directly: `Subgroup.IsComplement`, its `toRightFun` and
`mul_inv_toRightFun_mem` (Mathlib.GroupTheory.Complement), `Subgroup.index`
(Mathlib.GroupTheory.Index), ordinary linear maps/equivalences, and cochain-complex
morphisms in ModuleCat. Supporting retraction and argument definitions belong to the
owning averaging construction and are listed in `lean.declarations`.

Edge cases checked mathematically: H=G gives S={1}, r=id, T=R=id, and the identity
permutation. H={1} in a finite group gives r constant 1 and the usual finite sum.
A non-normal subgroup (for example a transposition subgroup in S3) still has the
right-coset permutation, because multiplication is on the right of Hs. Degree zero
uses one homogeneous coordinate; negative terms and all their maps are zero. The zero
coefficient module works. Characteristic dividing the index is allowed: only finite
addition occurs. Compact non-Hausdorff groups are not excluded. An empty transversal
cannot satisfy the complement condition for a group. No coefficient topology is
strengthened by the representation of cochains as abstract vector spaces.

Searches actually run:

- `msearch.py ... leanfinder "Finite coset averaging on jointly continuous homogeneous
  equivariant cochains for an open subgroup of a compact group"`: eight Haar-measure
  hits; none is this algebraic finite-sum cochain statement.
- `msearch.py ... loogle '"homogeneousCochains"'`: TopRep homogeneous cochains and
  algebraic group cochains. Read TopRep.homogeneousCochains and its differential:
  it is the iterated continuous-map topological-module model, not the given jointly
  continuous abstract function model, and has no required finite-coset averaging result.
- `msearch.py ... grep 'homogeneousCochains|transversal|corestriction'
  RepresentationTheory`: continuous cohomology and homology hits, no complete match.
- `msearch.py ... leansearch "Averaging continuous homogeneous group cochains over
  representatives of a finite index open subgroup gives a natural cochain map"`:
  algebraic cochain restriction, continuous homogeneous cochains, and
  `Representation.averageMap` (finite group and invertible order). None states this
  theorem without division or the supplied retraction and composite formulas.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for homogeneous cochains,
  finite-coset averaging, retraction, and the item id found the existing coordinate
  interface, parent inhomogeneous transfer, and internal-bar consumer. The parent is
  not imported. A search of `dag/lean_names_upstream.json` found no matching averaging
  declaration. Full proposed declaration-name searches in Mathlib and both project
  roots found no name collision.

Validation: the prescribed `scompile.py` compiled the module under both its sandbox
and final module names with no errors or warnings. An initial diagnostic required
`finiteCosetArgument` also to be marked noncomputable because it uses the canonical
noncomputable coset representative; this was corrected and compilation rerun cleanly.

## New nodes

`def-sfb-joint-continuous-cochain-coordinates` is a definition node with an
`existing: true` record for the exact existing structure
`ContinuousCohomology.JointContinuousCochainCoordinates`. This is the maintainer's
explicitly permitted definition-only attachment option. There is no new Lean module
and no duplicate definition. The existing theorem node bundles this structure in its
`lean.declarations` but its primary statement is an existence theorem; it does not
supply a definition node for a statement dependency.

The new node defines the complete existing interface: the topological field, group,
vector space and linear action are exactly the structure parameters; B and C are
integer-indexed abstract ModuleCat complexes with the chosen derived localization.
The injective evaluations and their exact images are `bEval/bInjective/bRange` and
`cEval/cInjective/cRange`; zero negative terms are `bNegative/cNegative`; the displayed
differentials are `delta/differential`. The actual isomorphism and its two evaluation
formulas are `iso/phi/psi`. Its derived realization and both arrow identities are
`derived/derived_hom/derived_inv`. Thus the definition does not silently omit the
inhomogeneous or derived fields even though averaging uses only its homogeneous part.
The definition itself does not add a joint-continuity hypothesis on the action: like
the existing structure it specifies data for a linear action; the averaging theorem
retains its explicit joint-continuity hypothesis. No field or universe is changed.
The `lean.statement` is copied verbatim from `structure` up to `where`.

Source: Stacks Tag 0DVG, `section-continuous-group-cohomology`, plus the agent-written
homogeneous coordinate expansion already documented on the existing structure.
I reread that source and every field in the structure, and the field/derived-category
dependency signatures. The latest blueprint direct-images paragraph (3) supplies the
arithmetic context; it does not print this auxiliary definition verbatim. Degree-zero
empty inhomogeneous tuples, one homogeneous coordinate, zero coefficients, negative
terms, arbitrary characteristic, independent universes and non-discrete topologies
are included exactly as before.

Searches for this attachment were run through `msearch.py` and recorded verbatim in
its `mathlib_searches`: LeanSearch for homogeneous and inhomogeneous jointly continuous
cochain coordinate data returned topological homogeneous cochains, algebraic cochains,
and Hom complexes, not this exact structure; Loogle for the quoted structure name
returned zero hits; Mathlib grep for the structure name and homogeneousCochains in
RepresentationTheory/Homological/ContCohomology returned 15 related cochain hits.
`rg` across dag/nodes, WeilConjectures and Sheaf found the exact existing structure
and its theorem node, with no independent definition node. Blueprint search for
"jointly continuous" returned zero matches. `blueprint_refs.py ancestor` again returned
None, so the new node uses null for the inherited broken ancestor chain, with the
item prepended to the inherited `via` list. The new node has the required H12 fields,
empty proof and proof dependencies, no Mathlib match, and an existing-declaration record.

## Repair of returned head abb2a2928a88

A2 and the mechanical theorem-in-statement-dependencies finding are repaired together:
removed `lem-sfb-topological-homogeneous-cochain-coordinates` from the item's added
statement dependencies and replaced it with the new definition node described above.
The existing:true option was explicitly authorized by the return. There is no
§1(B) dependency-module rewrite because no declaration needed to move. The item uses
the same coordinate structure, with unchanged Lean code, mathematical statements,
evaluation formulas, coefficient quantifier order, docstrings, and real helper data.
Compared the retained sandbox with the current read-clone main: the only differences
before repair were lean and stmt_deps; refreshed all non-owned fields from current main.
The prescribed delivery wrapper rebases the packet on current server main.
The maintainer had accepted all mathematical clauses and edge cases; this repair
changes the definition attachment and dependency classification it requested.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
