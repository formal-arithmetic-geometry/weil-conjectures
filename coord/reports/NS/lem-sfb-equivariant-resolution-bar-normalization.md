## Worker report

The module `Sheaf.CategoryTheory.EquivariantResolutionBarNormalization` states
`CategoryTheory.CondensedBar.equivariant_resolution_bar_normalization`, with `sorry`.
Its other seven public declarations are actual definitions or specifications for the
objects and canonical maps introduced in this very node. There are no additional
postponed theorems, new axioms, or choices of objects from mere existence assertions.
The accepted stage-1 split, all nine proof steps, and the source are preserved.

Hypothesis and clause correspondence:

- A commutative condensed ring on the small coherent profinite site: `A : Ring.{u}`,
  the existing `CommMon` of abelian sheaves on `coherentTopology Profinite.{u}`.
  Its underlying ring is `A.toMon : Profinite.CondensedRing`.
- Internal A-modules: `Modules A`, the existing `CategoryTheory.Mod` specialization.
  Coefficients lie in `u+1`, site parameters in `u`, and the ordinary derived
  localizations in `u+2`. No object/morphism universe equality is imposed on a site.
  This is the existing bar datum's size convention, not a new restriction.
- Profinite G and underline G(S)=C(S,G): explicit `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace` binders.
  The existing internal-action and parameter APIs use all continuous generalized
  elements and every profinite base change.
- N is an arbitrary internal module with trivial action: `N : Modules A`, followed
  everywhere by `(trivial (P := G)).obj N`. There is no topological presentation of N.
- Ordinary derived invariants: `M : Model A G`, `M.invariants.functor`, its upstream
  `rightDerivedFunctor`, and `rightDerivedFunctorUnitQ`. The abelian/Grothendieck
  infrastructure in the ambient binders and normalized models is supplied by the
  recorded restriction calculus and bar theorem, rather than an extra acyclicity
  assumption. The bar theorem asserts these models exist for every A and G; the
  result here holds for every such model, not a selected unnormalized one.
- R_N^n=underived internal Hom from the free A[G^(n+1)] to N:
  `HomogeneousBar.functions n` reuses the landed `HomogeneousFunctions` for trivial N.
  Its `internalHom` is an isomorphism to `homogeneousHom`, an actual
  `SheafOfModules.homObj` from the existing `CondensedBar.freeParameter` read through
  the recorded section-module equivalence. `HomogeneousBar.term n` is equivariant.
  There is no copied internal-Hom or free-module definition.
- The diagonal action `(g.f)(g0,...,gn)=f(g^-1 g0,...,g^-1 gn)` is the existing
  `HomogeneousFunctions.action`, whose value action is trivial for this N.
- The alternating deletion differential is `HomogeneousBar.differential`: the sum
  over `i : Fin (n+2)` with `(-1 : Z)^i.val` and deletion by `i.succAbove`.
  It is imposed on all generalized sections over every T -> S.
- The constant-function augmentation is `HomogeneousBar.augmentation`, with its
  value at every tuple fixed by `HomogeneousBar.constants` to restriction of N's
  original section. No arbitrary augmentation is substituted.
- All complexes vanish in negative degrees: R, K, U and the compatible total are
  indexed by N and mapped to ordinary Z-indexed complexes by the existing `extend`
  (extension by zero). This represents all nonnegative complexes; it is not a
  boundedness or finite-length restriction.
- The arbitrary equivariant quasi-isomorphism a:N[0] -> K is the binder `a` with
  `[QuasiIso a]`. Equivariant e:K -> R is `e`, and its required composite is exactly
  `hea : a ≫ e = H.augmentation`.
- U_N^n=underived Hom(A[G^n],N) with the trivial-action inhomogeneous differential:
  `(cochains M.bar).obj ((trivial (P := G)).obj N)`, reusing the recorded nerve
  faces, degeneracies, internal Hom and alternating-coface construction.
- Invariant homogeneous functions are evaluated at `(1,g1,g1g2,...)`:
  `prefixTuple` is the ordered product of the first j entries of `List.ofFn g`.
  The first coordinate is the empty product. `ResolutionEvaluation M H e rho`
  identifies each value of rho, after `M.bar.term`, with the existing homogeneous
  evaluation on the image of the invariant inclusion followed by e. Its equations
  quantify over n, S, x, T -> S and continuous tuples; they are not merely pointwise
  equations at the terminal test object.
- The resulting cochain map rho is the binder `rho` with precisely this defining
  formula `hrho`. It is not an unconstrained comparison map. Quantifying over such
  maps states the result for the canonical map without choosing from existence.
- The underived-to-derived arrow j is represented by a cochain map into the total
  for any compatible injective resolution I. `UnderivedBarComponents M N I j`
  fixes its entire n-th component to application of `I.ι.f 0` to function values,
  followed by the canonical `(n,0)` total coprojection. Thus `hj` is the definition
  of this canonical arrow, not an additional mathematical hypothesis or arbitrary
  map assumption. Two such chain maps are equal by componentwise extensionality.
- The compatible nonnegative resolution is `I : InjectiveResolution (trivial.obj N)`;
  the theorem holds for every I. `M.computation.forgetInjectives` identifies its
  underlying resolution as an ordinary internal-module injective resolution.
- The normalized derived bar isomorphism epsilon is `(M.computation.iso I).hom`.
  Its existing `normalization` field is `resolutionComparison` followed by Q of
  the total invariant augmentation, exactly the epsilon fixed by the cited node.
- Q is `DerivedCategory.Q`. `localizedAugmentation a` inserts the canonical
  `extendSingleIso` between N[0] and extension of the nonnegative single complex,
  then localizes a. `invariantUnit M.invariants K` inserts `mapExtendIso.inv` and
  applies the canonical `rightDerivedFunctorUnitQ`; its source is Q((K)^G).
- Finally the conclusion is Q(rho) ≫ Q(j) = u_K ≫ (RF(Qa))^-1 ≫ epsilon.
  Lean composes left-to-right, so this is exactly the node's
  j o Q(rho) = epsilon o (RF(Qa))^-1 o u_K. It is equality of derived arrows,
  with the full derived bar isomorphism, rather than equality only on cohomology.
- No acyclicity of K^n or R_N^n is assumed: inspect the complete signature, which
  contains only `[QuasiIso a]`, the augmentation equation, and the two defining
  component formulas. In particular neither `Injective (K.X n)` nor invariants-
  acyclicity of K or H appears.

Dependency declarations used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, through the
  existing action/bar public imports; the commutative bundled form is `CondensedBar.Ring`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, through `Modules`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `trivial`,
  `Invariants`, `Invariants.inclusion` and the actual equivariant category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.singleFunctor`.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: the recorded calculus,
  in particular its `boundedBelowComputation`, publicly imported for the shared
  canonical ordinary-derived-invariant framework.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  general universal-pair interface. The bar's own existing `Computation` specializes
  to the upstream `Functor.rightDerivedFunctor`; these are the same total-derived
  notion up to the unique unit-compatible isomorphism. No second RF is defined here.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`:
  `Functor.rightDerivedFunctorUnitQ`, the canonical unit with source Q(FK).
- `Sheaf.CategoryTheory.CondensedDerivedInvariantBar`:
  `condensed_derived_invariant_bar`, supplies the normalized models used by the theorem.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `Ring`, `Modules`, `Model`,
  `sections`, `power`, `tupleMap`, `cochains`, `doubleComplex`, `totalCochains`,
  `extend`, `Computation.iso` and its normalization. Its landed id is added to
  `stmt_deps`, as permitted for existing landed notions.
- `Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective`: the existing
  `homogeneousHom`, `homogeneousEvaluate`, and `HomogeneousFunctions` definitions,
  owned by the new definition node `def-sfb-condensed-homogeneous-functions`.
  The theorem `homogeneous_functions_injective` is used only by the proof plan.
  Neither this module nor its node is changed or delivered.
- Proof-only imports retain all recorded, stated proof dependencies: Grothendieck
  enough injectives, injective resolutions, K-injective computation, the internal
  section equivalence, extension-by-zero flatness, tensor closedness, preservation
  of injectives by right adjoints, homogeneous functions injective, double-complex
  totals, injective lifting and homotopy uniqueness. Their nine-step use is spelled
  out in the main theorem's docstring. The section equivalence and injective
  resolutions are already public imports of the statement dependencies.

Edge cases checked:

- n=0: the inhomogeneous tuple is empty; `prefixTuple` has the single coordinate 1.
  The homogeneous differential is the difference of the two deletions, as required.
- Noncommutative G: `List.prod` preserves the order g1,g2,...; no commutativity of G
  is assumed and prefixes are not expressed using unordered finite-set products.
- Trivial G: the formulas remain defined; the unit/augmentation normalization is
  unchanged. The theorem does not discard this case.
- N=0 and the zero coefficient ring: all categories, internal Homs and augmentations
  still make sense and there is no nonzero hypothesis.
- Empty profinite test spaces are included by quantification over all Profinite.
  No global-point-only criterion is used for equality of internal maps.
- Arbitrarily long K and I are allowed. Every total degree has the existing finite
  diagonal but no uniform bound is imposed.
- No injectivity is claimed of section modules N(S). The internal-Hom model is on
  the entire slice, so this does not conflate internal functions with point values.

Searches performed before writing:

- `msearch.py ... leanfinder`: "An augmentation preserving map from an equivariant
  resolution to the homogeneous group bar resolution induces the canonical derived
  invariants comparison". Eight hits, including `Rep.barResolution`,
  `Rep.barResolution.extIso`, `groupCohomology.infNatTrans`; these concern ordinary
  representations and do not state this internal condensed derived-arrow equality.
- `msearch.py ... loogle`: `CategoryTheory.Functor.rightDerivedFunctorUnit`.
  Service answered unknown identifier (the unit is a project declaration, not a
  Mathlib one). Direct source inspection found the exact canonical `UnitQ` API.
- `msearch.py ... grep`: `homogeneous|barResolution` in `RepresentationTheory`.
  Twenty-five hits include `TopRep.homogeneousCochains` and `Rep.barResolution`.
  They use topological or abstract representations, not internal condensed modules.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for homogeneous evaluation,
  equivariant normalization, resolution/bar names and the item id. The ordinary
  topological homogeneous/inhomogeneous comparison is upstream, while the internal
  homogeneous functions and bar model are already landed. They are reused, not copied.
  The item is cited only by the polynomial comparison's proof docstring; no existing
  declaration states this theorem. Searching this item's id in `WeilConjectures`
  returned no declaration.
- `tools/blueprint_refs.py search homogeneous` and DAG searches confirmed that the
  homogeneous-function notion belongs to the landed node now cited. The current
  maintainer return requires reusing the existing three definitions from CondensedHomogeneousFunctionsInjective. The other helpers here specify
  the R, rho and j introduced by the item itself.

No statement correction and no STATEMENT-DISPUTED flag. There is no repair-note file
for this item. The predecessor's unchanged-node failure concerned its stage-1 copy;
this delivery makes a real `lean` binding and keeps that accepted split intact.

## Second reading by NS

In-session second reading, with the node and completed Lean module reopened; no other
agent was started, as explicitly required by the dispatcher. The maintainer supplies
independent mathematical review after delivery. This section does not claim a separate
worker's review.

Checked every hypothesis and clause against the correspondence above. In particular,
R uses the existing slice internal-Hom model; its action includes the inverse on every
argument, and trivial coefficients remove the value action. The differential has n+2
faces and the signs (-1)^i. The prefix list uses j entries, so degree zero is 1 and
its last coordinate is g1...gn. The rho formula first includes invariant sections,
then applies e, then changes to homogeneous coordinates. The j formula puts values
into total bidegree (n,0), while the existing normalized epsilon uses the invariant
augmentation in (0,q). Composition order in the final equation agrees with the node.
The only assumptions on K are a's quasi-isomorphism and preservation of the constant
augmentation; all complexes are nonnegative by their natural indexing.

The compiler originally could not synthesize `IsIso` for an opaque extended augmentation.
The final definition `localizedAugmentation` explicitly constructs its canonical iso
using `Q.mapIso (extendSingleIso ...).symm` and `asIso (Q.map (extendMap a ...))`.
This inserts no hypothesis and changes neither the ordinary object nor the map. A
long-line warning was corrected without changing any term. The recorded signature
is extracted verbatim from the final file, including its line breaks.


## Repair of return ab4904d3c220 (H2)

Added `def-sfb-condensed-homogeneous-functions` as an existing:true definition
node for the three plain definitions in the UNCHANGED module
`Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective`. Replaced the
injectivity theorem node in the item's stmt_deps with this definition node;
the theorem remains in proof_deps. The main Lean file is byte-identical to the
returned version. No definitions were moved, copied or renamed, and the
injectivity dependency node/module is not delivered or edited. The node's TeX,
proof and proof_deps are unchanged. This repairs the returned H2 ownership fault.

## New nodes

`def-sfb-condensed-homogeneous-functions` records existing `homogeneousHom`,
`homogeneousEvaluate`, and `HomogeneousFunctions`, from lines 45-84 of
`Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective`. The definitions
use no result from the later existential injectivity theorem. The source is
paragraph (3) of the current main blueprint direct-images proof, the homogeneous
helper's displayed action formula, and Stacks 03EO for slice sheaf Hom.

Clause correspondence: `R : Profinite.CondensedRing.{u}` and `[IsCommMonObj R.X]`
express arbitrary commutative condensed coefficients; the explicit topological
and group binders express profinite G; `J : ActionModule R G` is arbitrary;
`n : ℕ` covers every nonnegative degree. `homogeneousHom` uses the existing
`freeParameter` and `power` (def-sfb-condensed-equivariant-bar-data), then
`sectionModuleFunctor` (def-weil-pbc-internal-abelian-sheaf-module-equivalence)
and `SheafOfModules.homObj` (def-pur-sheaf-hom). `homogeneousEvaluate` applies
`c.app (op (Over.mk f))` to `InternalBar.generator` from
`def-sfb-condensed-free-module-generators`. The structure fields `object`,
`internalHom` and `action` retain precisely the equivariant model, its actual
internal Hom identification and the displayed action on every profinite slice.
The inverse acts by left multiplication on every argument, followed by `J.act`
on the value. There is no existence or injectivity assertion in this definition.
All four specified dependency records, signatures and source bodies were read.

LeanSearch and LeanFinder were rerun with the query "Internal homogeneous functions
on powers of a profinite group with diagonal action on arguments and coefficients";
the hits concern ordinary representations, topological continuous cochains and
profinite group homomorphisms. Mathlib grep for
`homogeneousCochains|homogeneousHom|HomogeneousFunctions` returned TopRep cochains,
not this internal slice notion. Project rg found exactly the three existing
public definitions, plus an unrelated private graded-algebra homogeneousHom.
DAG search found no definition owner; blueprint_refs search homogeneous returned
40 other nodes and ancestor returned None. All search outputs are retained in
the search log and the new node's mathlib_searches. The return specifically
requires recording these existing definitions, with no new Lean module.

## Second reading by NS (ab4904d3c220 repair)

Reopened both packet nodes, the unchanged item module and the existing definition
module. The new definition node matches the three declarations clause by clause
as described above. The item's stmt_deps now names that node, while proof_deps
still names the injectivity theorem. It no longer relies on an existential theorem
as the owner of plain definitions. The item retains all previously rechecked
clauses and all nine proof steps: slice-pinned action/differential/augmentation,
ordered prefixTuple, j through I.ι.f 0 into (n,0), normalized Computation.iso,
canonical rightDerivedFunctorUnitQ, the composition order and no acyclicity
hypothesis. Checked n=0, noncommutative and trivial G, N=0, zero ring and empty
test spaces; the new definition also allows arbitrary J and its value action.
No Lean byte changed and no new sorry or axiom was introduced. This was an
in-session self-check; no other agent was started, as required by the dispatcher.

## Validation of repair ab4904d3c220

The prescribed initial dry run of the retained packet passed at 837b41e0959.
That confirmed its baseline shape and compile; the requested definition-ownership
repair was then added. Explicit scompile.py of the unchanged normalization module
returned exit 0 (sandbox 34.2 s, library 38.5 s), with no unexpected warnings.
The theorem signature matches lean.statement verbatim; autoImplicit is false;
all Lean lines are at most 100 characters. JSON uses indent 1, ensure_ascii false
and a final newline. Relative to the read clone only lean and stmt_deps change
on the item; the new definition node is existing:true and delivers no Lean file.
The item Lean SHA256 is
c5fe4b92da49735f5ff626d6d827fcaa9c11586dc0fc07c69470ed9cecd1c07e.

The repaired packet's deliver2.py --no-push passed at f34ff8af4cc: the
existing-definition check, preflight and per-file compiles all succeeded.
Its staged set is exactly this report, the new definition node, the item node
and the unchanged normalization module. No dependency module or moved definitions
are included. Final delivery uses the same prescribed wrapper on current main.
