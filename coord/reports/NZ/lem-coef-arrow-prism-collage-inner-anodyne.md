## Worker report

Repaired the returned packet at immutable head `03846cedd48b`; the saved packet's
initial dry run passed at `acc27dd283`, but its substantive defects remained and
have now been repaired. The delivery preserves the module's normal-form construction
and changes only the item's `lean` record. Comparing the sandbox node with current
main found no difference outside `lean`; the delivery wrapper rebases the packet.
No new node, dependency repair or informal statement correction is needed.

The module is `lean/Sheaf/CategoryTheory/ArrowPrismCollage.lean`. Its theorem is
`SSet.Enhanced.arrowPrismCollageInnerAnodyne`. All thirteen declarations are recorded
in `lean.declarations`. Every definition has real data; all five theorem proofs
are `sorry` as required for stage 2. The four construction obligations have source,
blueprint and complete natural-language proof docstrings under this same node.

Hypothesis and clause correspondence (write `v = arrowPrismTarget X B`,
`J = relativeJoin v (𝟙 X)` and `e = relativeJoinSnd v (𝟙 X) ≫ fst _ _`
in this explanation only):

- Small simplicial sets in a fixed arbitrary universe: `universe u`, `X : SSet.{u}`.
  No quasicategory instance is required. All other simplicial sets remain in u.
- The specified simplicial subset of the arrow object is the actual binder
  `B : ((ihom Δ[1]).obj X).Subcomplex`, not an arbitrary simplicial set.
- Target evaluation is fixed by real construction:
  `arrowPrismTarget X B = B.ι ≫ evaluation Δ[1] X (stdSimplex.obj₀Equiv.symm 1)`.
  There is no arbitrary map or additional hypothesis standing in for evaluation.
- The join is the dependency's exact `relativeJoin v (𝟙 X)`. Its second projection
  records both the block parameter and the target-coordinate simplex σ. Its first
  projection records the ordered-join datum, so the initial prism q is the B datum
  restricted to the initial block. Empty blocks use the dependency's augmentation.
- The nerves P_x and all their simplex-operator identifications are represented by
  their degreewise normal form `arrowPrismP`: pairs `(r,y)` satisfying
  `arrowPrismIntervalLE (e.app n y) r`. The two interval arguments have been swapped
  in BOTH `arrowPrismP` and `arrowPrismP_map`. Pointwise interval order is the order
  on the corresponding monotone maps `[n] → [1]`. Node proof step 1 and theorem
  docstring step 1 give explicit inverse quotient identifications: a chain maps to
  its row and restricted support; `(r,y)` is represented in P_y by s_k if r(k)=0
  and t_k otherwise. Cross relations and all operators match precomposition.
- Q_x's target simplex becomes `{1} × J`; its initial prism becomes `Δ[1] × J₀`.
  Accordingly `arrowPrismQ` is exactly the union of the products of the vertex-one
  subcomplex with J and the full interval with `arrowPrismInitial`, whose defining
  equality is `e(y)=0`. Here J₀ is the simplicial fibre, not just its vertices.
- Arbitrary H is the binder `H : J.Subcomplex`. The union of its P_h supports is
  `arrowPrismPH`, defined by `e(y) ≤ r ∧ y ∈ H.obj n`; its operator obligation
  `arrowPrismPH_map` uses the corrected inequality in both hypothesis and conclusion.
  This is precisely P intersected with the inverse image of H (node proof step 2).
- `arrowPrismQH` is the lattice union Q ⊔ P_H. The named inclusion fact
  `arrowPrismQH_le_P` now has a true statement: e(y)≤1 on the target row, 0≤r on
  the initial fibre, and the defining inequality on P_H. `arrowPrismQHToP` is
  `Subcomplex.homOfLE` of that fact, hence the canonical relative inclusion.
- Inner anodyne is exactly the first conjunct
  `SSet.innerAnodyneExtensions (arrowPrismQHToP X B v H)`.
- A simplicial map `ev : Q ⟶ X` is supplied, with TWO actual restrictions. The first
  quantified equation says that if a Q simplex z has row identically one, then
  `ev.app n z = (relativeJoinProjection v (𝟙 X)).app n z.val.2`, i.e. σ.
  The second says that if its support is `relativeJoinInl v (𝟙 X)` applied to b,
  then its value is `((ihom.ev Δ[1]).app X).app n (z.val.1, B.ι.app n b)`, i.e.
  b(r). The inl image is exactly J₀ by the dependency's pure-factor formula and
  the pullback definition. These implications state restrictions on all simplices
  of the corresponding subcomplexes; neither chooses nor excludes any simplex.
  On `{1} × B`, both restrictions give target evaluation by the definition of v.
- The map `d : J ⟶ P` has the full coordinate prescription, for every degree n
  and y, `(d.app n y).val = (e.app n y, y)`. Thus d chooses exactly the source
  vertices of the initial block and target vertices of the final block. This is
  the stated chain and includes both pure-factor conventions.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: Mathlib SSet/internal hom/nerve/product
  conventions, and `SSet.Enhanced.evaluation` with its full vertex-evaluation signature.
  The internal evaluation counit is Mathlib's `(CategoryTheory.ihom.ev Δ[1]).app X`.
- `Sheaf.CategoryTheory.RelativeJoin`: `SSet.Enhanced.relativeJoin`,
  `relativeJoinSnd`, `relativeJoinProjection`, `relativeJoinInl` (and its defining
  `relativeJoinLift`/endpoint formula). Their full source and docstrings were read.
- `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`:
  `SSet.innerAnodyneExtensions_pushoutObjObjι'`, the recorded Mathlib match for
  `lem-coef-inner-anodyne-pushout-product`; the lifting-class definition
  `SSet.innerAnodyneExtensions` was also read in Inner/Basic.lean.
- Proof-only import `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate` supplies the
  recorded proof dependency `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`:
  `SSet.exists_nonDegenerate`, `unique_nonDegenerate_dim`,
  `unique_nonDegenerate_simplex`, `unique_nonDegenerate_map`; signatures were read.

Edge-case checks: X=B=Δ⁰ gives J=Δ¹, P=Δ² and Q=Λ²₁. In particular the returned
counterexample `(1,y)` with e(y)=0 now satisfies the defining inequality `0 ≤ 1`.
The target row always satisfies e(y)≤1; the initial prism always satisfies 0≤r.
For B empty, J is the pure final factor, so P=Q and the evaluation prescription
is the target projection; the prism restriction has no b. For X empty, B and J
are empty and the asserted maps are the unique empty maps. For H empty the
inclusion is Q↪P; for H=J it is the identity. At a pure initial support e=0, d
uses row zero; at a pure final support e=1, it uses row one. Mixed support uses
exactly the displayed s/t chain. The diagonal inequality is reflexive in every
degree, including degree zero. Degenerate simplices and all operator restrictions
are retained by the subcomplex definitions; no nondegeneracy hypothesis appears.
All universes and variables are explicitly bound with `autoImplicit false`.

Searches run on 2026-10-18: `msearch.py NZ lem-coef-arrow-prism-collage-inner-anodyne
leanfinder "arrow prism collage relative inner anodyne"` returned only generic simplicial
horn/pairing infrastructure; `... loogle "SSet.innerAnodyneExtensions, SSet.Subcomplex.Pairing"`
returned the generic Mathlib class and no exact collage statement; `... grep
"collage|triangular|innerAnodyne" AlgebraicTopology/SimplicialSet` found only generic horn and
pairing files. `rg -n "arrowPrism|collage|relativeJoin"` in the project and source found no
existing declaration of this notion. The dependency modules and the existing stage-2 modules
were searched before defining the helpers; no duplicate project or upstream declaration exists.

Additional repair searches: `msearch.py ... loogle
"SSet.Enhanced.arrowPrismTarget, SSet.innerAnodyneExtensions"` returned zero hits
(unknown specialized target-evaluation name); `msearch.py ... grep
"arrowPrism|triangular|collage" AlgebraicTopology/SimplicialSet` returned zero hits.
`rg -n "arrowPrism|triangular.*cylinder"` over both upstream WeilConjectures and
project lean/Sheaf returned zero hits, as did the item-id search in upstream.
The repair also opened https://kerodon.net/tag/0302, especially the construction
of S from arrow evaluation and the relative join. As the node source explicitly
says, the relative staircase formulation is the agent-written expansion, not a
verbatim claim of that page.

No remaining `STATEMENT-DISPUTED` flag or node fault is asserted.

## Second reading by NZ

This is the required separate self-check with both node and final file open; the
dispatcher's explicit instruction prohibits starting another agent. The previous
second reading was defective. This reading checks the actual predicates and
conclusion equations, not their names or the old report.

H3/H6, support orientation: read each occurrence of `arrowPrismIntervalLE` in P,
P_map, PH and PH_map. Every occurrence now has e(y) as the FIRST argument and r
as the SECOND. The inclusion obligation is consequently true on both Q summands.
The concrete counterexample from the return is included, not excluded.

H3, arrow data: the theorem binder is the actual Subcomplex of `(ihom Δ[1]).obj X`.
Read `arrowPrismTarget`: inclusion followed by the dependency's evaluation at 1.
General X/B/v binders remain only on the valid ambient support constructions;
the main theorem always instantiates them with the specified B and this fixed v.

H3/H6, evaluation: read the first restriction's antecedent (constant row one) and
its RHS (`relativeJoinProjection`), and the second restriction's antecedent
(support is the initial-factor inclusion of b) and its RHS (internal evaluation
at row r of B.ι(b)). Both are real constraints, covering the two summands of Q.
Their common row-one/initial-factor value is exactly v(b); no tautology remains.

H3, diagonal: read the last quantified equality after both existential maps.
It prescribes BOTH ambient coordinates as `(e(y),y)`. This is the exact chain in
the node, including the pure initial and pure final cases. Existence alone is
no longer the conclusion.

H8, docstrings: all thirteen declarations now have source/blueprint docstrings.
Each of the four support construction theorems has its explicit natural-language
proof; the main theorem carries all nine steps of the DAG proof. The helper
record includes every declaration, and the main signature is copied verbatim.

The final statement retains arbitrary H, all small simplicial sets X, empty and
pure-factor cases, and no quasicategory condition. The actual node statement,
source, dependencies and proof have not been altered. The repaired file compiles
cleanly through the required scompile.py wrapper; delivery preflight and per-file
compilation are rerun on this repaired packet before pushing.
