## Worker report

The module `Sheaf.CategoryTheory.LatticeKoszulTotalTriangles` states the structural
properties of the existing signed lattice Koszul total. The main declaration is
`Profinite.DiscreteLattice.TotalTriangles.lattice_koszul_total_triangles`.
All nine theorem proofs are `sorry`; `ConeComparison` and `Descent` specify data and
laws, and `connectingPlus` is an actual canonical construction, with no sorry data.
The node is unchanged except for `lean`.

Hypotheses and objects, clause by clause:

* A commutative condensed ring on the small coherent profinite site is
  `R : Profinite.CondensedRing.{u}` with `[IsCommMonObj R.X]`. This is the recorded
  general internal ring, not a ring assumed to come from a topological ring.
* The size convention is the explicit universe `u` of the profinite site, internal
  abelian sheaves in universe `u+1`, and the recorded standard derived localization
  universe `u+2`. There is no restriction equating unrelated universes.
* `r : ℕ` includes rank zero. `Group r` is the dependency's multiplicative notation
  for `Fin r → ℤ`; `Modules R` is its internal module category and `Equivariant R r`
  its discrete action category. This uses the exact category and discrete-action
  specialization already recorded by the Koszul dependency. No alternate category
  or action data is introduced. Trivial action and invariants are the background
  functors of the dependencies; this structural calculation adds no hypothesis on them.
* `K : KoszulModel R r` uses the dependency's finite subset coordinates, exact ordered
  differential `differentialEntry`, and diagonal map formula `maps`. The result is
  uniform in such a model. These coordinates determine the complex up to its indicated
  natural coordinate isomorphism; this is not an unconstrained complex parameter.
* The actual total is the already published `TriangulatedCup.total R r K`, namely
  map the input complex by K, flip to put Koszul degree first, then apply Mathlib's
  `HomologicalComplex₂.totalFunctor`. It has terms the diagonal sums and differential
  `d_K + (-1)^a d_P`. No new definition of this notion was made.
* Exactness of every `K^a` is `terms_exact`: additivity and preservation of finite
  limits and colimits of `K.functor ⋙ HomologicalComplex.eval ... a`, for every
  integer `a`, including the zero functors outside the Koszul strip.
* Additivity of totalization is `total_additive`. Its restriction to bounded-below
  complexes is the existing `TriangulatedCup.totalPlus`. `total_lower_bound` spells
  out preservation of every actual termwise lower bound, so the D-plus codomain
  does not follow merely from a cohomological boundedness assumption.
* The homotopy is `total_homotopy`: it gives `H : Homotopy (Kf) (Kg)` and the formula
  after every total-summand inclusion is `a.negOnePow • K^a(h^b)` followed by the
  corresponding target inclusion. The b,c relation is precisely the degree -1
  relation. `Homotopy.zero` supplies the vanishing outside that relation.
* Quasi-isomorphism preservation on bounded-below complexes is `total_quasiIso`,
  using the actual maps `f.hom` and `QuasiIso`. The ordinary localization is Mathlib's
  `DerivedCategory.Q`, with the actual bounded-below derived categories in `Descent`.
* Every integer shift has the existing natural chain isomorphism
  `TriangulatedCup.totalShiftIsoApp`. `shift_coordinates` gives its scalar
  `(a*s).negOnePow`, after the canonical degree reindexing isomorphisms. Naturality
  and zero/addition coherence are already the published `totalShiftNaturality` and
  `totalShiftCoherence`; `totalCommShift` uses exactly these isomorphisms. Both
  positive and negative shifts are included, without a natural-number restriction.
* `ConeComparison.iso` is the actual chain isomorphism
  `K(Cone f) ≅ Cone(Kf)`. Mathlib's mapping cone uses the direct sum of shifted source
  and unshifted target, canonically the same as the statement's reverse ordering.
  Its differential is `(dy+fx,-dx)` in the node's ordering. `inclusion` asserts identity
  on the unshifted target summands; `shifted` gives exactly `a.negOnePow` on the shifted
  source summands. Every summand is specified by the existing bicomplex inclusions.
* Naturality of these cone isomorphisms for every commutative square is
  `ConeComparison.naturality`. `lastArrow` states compatibility with the cone
  triangle's actual third arrow, which is `-p`. Since the functor is additive, this
  also gives the unsigned projection equation. Shift naturality/coherence are the
  existing laws above. `cone_comparison` asserts existence of all these data and laws.
* `Descent.functor` has source `DerivedCategory.Plus (Equivariant R r)` and target
  `DerivedCategory.Plus (Modules R)`. `Descent.factor` identifies its composition
  with localization with the actual total followed by Q. `commShift`, `triangulated`,
  and `factorShift` specify triangulation and descent of the already fixed shift
  comparison, rather than an arbitrary triangulated functor or arbitrary shifts.
* Termwise short exactness is `total_shortExact`. `S.ShortExact` in the abelian
  category of complexes is exactly degreewise short exactness. The proof plan notes
  that this finite-strip statement, like the homotopy and cone calculation, does
  not require the lower bound; the result in particular applies to all input complexes.
* `connectingPlus` transports Mathlib's `DerivedCategory.triangleOfSESδ` to D-plus
  by the fully faithful inclusion, using the quotient/Q and shift identifications.
  `Descent.connecting` states the exact boundary equation after localization and
  the factorization isomorphism. Thus the canonical connecting arrow, not just an
  unspecified distinguished triangle, is preserved. The definition uses a preimage
  under a fully faithful functor, not an arbitrary morphism or an existence choice.

Dependencies read and used:

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, including its
  original coherent profinite-site and ring-object encoding.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj` and compatible
  module morphisms; specialized by `Profinite.CondensedAction.Modules` in
  `Sheaf.CategoryTheory.CondensedActionModule`. That module's `ActionModule`,
  `Equivariant`, `forgetAction`, `trivial` and inflation interface were read.
* `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`: `Modules`, `Group`,
  `Equivariant`, `KoszulModel`, `Subsets`, `differentialEntry`, `invariants`, and
  `modulesDerived`/`equivariantDerived`. The full KoszulModel signature and docstring
  and the main resolution statement were read, including its normalization.
* `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: the recorded restriction,
  coefficient and cup calculus, whose full coefficientSquare signature and module
  proof plan were read. It provides the general action/invariants context; no cup
  comparison theorem is assumed for this structural total calculation.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, Q and `quotientCompQhIso`; `Plus` gives the actual D-plus
  categories and their fully faithful inclusions.
* Proof imports: `Functor.homologyFunctorIso` from
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`;
  `HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns` from
  `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`;
  `Functor.IsTriangulated` from `Mathlib.CategoryTheory.Triangulated.Functor`;
  `CochainComplex.mappingCone.quasiIso_descShortComplex` from
  `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`. Their signatures/docstrings
  were read. These are the recorded proof dependencies, not unstated new prerequisites.

Existing helper ownership and import direction:

`Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison` already owns `total`,
`totalPlus`, `bicomplex`, the signed shift comparison and its naturality/coherence.
These definitions/laws, not its derived-invariants or cup-comparison theorem, are reused.
It currently has no source import of this new module. The DAG records this item as
its proof dependency. The maintainer must NOT add the reciprocal proof import to that
module, since it would close a Lean import cycle (stage-2 rule 7 explicitly exempts
such additions). No reverse DAG dependency was introduced, no agent was waited for,
and no duplicate total or shift definition was written. A future ownership refactor
could move the existing elementary construction to a common module; that is outside
this delivery's read-only scope. The actual declarations reused here have their own
explicit elementary coordinate proof plans and do not assume the comparison theorem.

Edge checks before writing: r=0 gives the sole empty subset in degree zero and the
underlying complex; all total, homotopy, shift and cone signs are 1. Negative/out-of-strip
Koszul degrees have empty finite coordinates. Zero modules and the zero coefficient
ring give zero sums and maps. Inputs can start in any negative or positive integer
degree. Negative shifts use `Int.negOnePow`, so do not require a negative natural power.
The zero map's cone tests both summand families and distinguishes the sign on the
shifted one; characteristic two identifies the signs automatically. The last-arrow
and boundary equations deliberately use Mathlib's signed third arrow, not an unsigned
projection. No boundedness of the cone beyond that of its inputs is assumed.

Searches (all through the required msearch.py wrapper unless indicated):

* LeanFinder: "Finite Koszul totalization of equivariant complexes preserves
  quasi-isomorphisms shifts cones and short exact sequence connecting maps" returned
  the cone/short-exact quasi-isomorphism and related homology results; no full match.
* Loogle: `"total", "shift"` returned the two bicomplex total-shift isomorphisms and
  their component/naturality lemmas, including `totalShift₂Iso`. They supply the
  existing shift implementation, not the complete structural result.
* Mathlib grep: `koszul.*(total|triangulat)|total.*koszul` returned zero hits.
* LeanSearch: "Finite signed Koszul totalization preserves quasi-isomorphisms and
  distinguished triangles" returned homology-preserving quasi-isomorphism lemmas and
  `HomologicalComplex₂.total.mapIso`, not this complete lattice result.
* `rg` with the Koszul/total pattern and the exact item id in `lean/WeilConjectures`
  and `lean/Sheaf` found the published `LatticeKoszulTriangulatedCupComparison` helpers
  above, as well as unrelated tensor/Koszul completions. That complete module was
  opened, and no existing theorem states all the item's homotopy, cone, exactness,
  localization and connecting-arrow clauses. The recorded Koszul dependency was also
  opened rather than inferred from its declaration name.

Source checked: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
which supplies the direct-image route. The structural calculation is explicitly the
agent expansion recorded by this node, with its eight-step proof and Stacks sign
conventions. No statement correction, new definition node or dependency repair is needed.

Validation: the required module-mode server compilation was used for the diagnostic
probe and the delivered module. The initial check found only an index equality that
needed unfolding of the total-degree map before `omega`; this was repaired. Final
compile and delivery preflight results are recorded below.

## Second reading by Q69

A separate second pass matched the node and completed source file clause by clause.
No separate agent was started, as the dispatcher expressly prohibits doing so; the
maintainer supplies the independent review specified in this assignment.

The ring, site and size binders use the recorded general condensed-ring/module types;
there is no topological-origin, flatness, injectivity or positive-rank assumption.
The total is the existing Koszul-first total, not an alternate or arbitrary functor.
Exactness covers all Koszul degrees; lower bounds are termwise; the homotopy formula
has the required column sign. The shift equation reindexes both the input and total
terms explicitly and uses integer signs, including negative shifts. The cone's two
families are distinguished by inclusion and shifted formulas; its naturality equation
covers every commutative square and the third-arrow equation retains the minus sign.
The descent is triangulated between ordinary D-plus categories, identified with the
actual Q of the actual total, and its shifts are fixed by `factorShift`. The final
boundary equation is for `triangleOfSESδ`, transported through canonical quotient
and shift identifications, so an arbitrary boundary cannot satisfy the specification.

The reading also checked for duplicate constructions and import cycles: published
`total` and shift helpers were reused, while no statement dependency on the downstream
cup theorem was added. The only elaboration repair was unfolding the total diagonal
index before arithmetic; it changes no mathematical hypothesis or clause. Definitions
contain real data; all postponed theorems have source/proof docstrings under this node.

Final validation: scompile.py passed for sandbox and library module names (24.5 s and
24.8 s) with no errors or warnings. deliver2.py --no-push printed
`OK (dry run): commit 4dda9112e34 passes the preflight and compiles; nothing pushed`.
