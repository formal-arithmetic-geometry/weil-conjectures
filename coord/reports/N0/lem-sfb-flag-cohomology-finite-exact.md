## Worker report

The delivery states `AlgebraicGeometry.flag_cohomology_finite_exact` in
`Sheaf.AlgebraicGeometry.FlagCohomologyFiniteExact`. It adds two definition modules:
`RationalCharacterFiltration` and `HomogeneousVectorBundle`. The original item's
statement, proof plan and proof dependencies are unchanged. Its statement dependencies
gain the two new definition nodes. All theorem proofs, including the four named
well-definedness helpers in the new definitions, are `sorry`. Definitions have actual
data; none chooses unspecified bundle or cohomology data from an existence theorem.

Hypotheses and notation, clause by clause:

- The field is `F : Type u`, `[Field F]`, `[IsAlgClosed F]`; positive characteristic is
  `p : ℕ`, `[Fact p.Prime]`, `[CharP F p]`. This excludes characteristic zero exactly
  as the node does.
- `S : Grp (Over (Spec (.of F)))` is the given algebraic group. `hS` is the existing
  `IsSemisimpleGroupScheme S.X`. `hsc` is verbatim the central-isogeny definition used
  by `exists_rho_section_modules`: all surjective finite-central-kernel maps from
  semisimple group schemes are isomorphisms. Affineness is made explicit for the
  canonical coordinate Hopf algebra; it is inherent in these algebraic groups.
- The inclusions `iT`, `iB`, `im`, `j`, `jm` are the torus and two Borel inclusions.
  `hpair` and `hpairm` use the recorded `IsRhoBorelPair`, so include the closed subgroup,
  split maximal torus, Borel, and factorization requirements, not arbitrary maps.
- `aB`, `am`, `hB`, `hm` use the actual torus conjugation actions. `Φ`, `hΦ` enumerate
  precisely the nonzero weights in Lie(B); `hopposite` says precisely that Lie(Bm)'s
  nonzero weights are their negatives, using inversion of characters. This is the
  node's positive-root and opposite-Borel convention. `Φ.card` is N. Root lattices,
  coroots, rho, the Weyl group and dot action are contextual notation not used by any
  conclusion of this node; they introduce no extra parameters or hypotheses here.
- Finite rational modules are the existing `EquivariantCoherent.Representation`,
  with their actual vector spaces, finiteness, coordinate coactions, counit and
  coassociativity. Morphisms use its existing `IsRepresentationMap` identity.
  Rational subspaces and simple modules use `RationalHighestWeight.IsStable` and
  `IsSimple`; subquotients are the new explicit `IsSubquotient` predicate.
- A character module is `characterModule χ`, whose space is F and whose coaction is
  `a ↦ a ⊗ characterElement χ`. Characters are represented as characters of Bm;
  their restriction to T is `jm ≫ χ`. This is the equivalent Borel-character encoding
  of the node's F_x, since restriction from a split Borel to T identifies character
  groups. Filtration factors explicitly have trivial action of the unipotent radical:
  the displayed identity is required on every smooth connected normal unipotent closed
  subgroup, which includes that radical (and is equivalent to killing it).
- `Q`, `π` specify the quotient by a faithfully flat right torsor: flatness,
  surjectivity, and the exact `IsPullback` square for (g,b) ↦ (g,gb).
  Properness and finite type are the standard quotient properties. This identifies
  the fppf quotient, rather than allowing an unrelated proper scheme.
- `D : HomogeneousVectorBundle.System S Bm im Q π` supplies the actual sheaves L(M).
  Its natural coordinate trivializations on every test scheme, together with
  `coordinate_orbit`, are exactly f(gb)=b inverse f(g). `map_coordinate` fixes the
  functor's coefficient maps, while its algebraic action and `linearization_coordinate`
  fix left translation f(g) ↦ f(s inverse g). The theorem asserts finite local freeness
  of rank `Module.finrank F M.space`, the sheaf form of the associated vector bundle.
- Nonnegative cohomology is the existing `HOver Q.hom (D.L M) i`, i.e. actual Zariski
  sheaf cohomology with structural F-scalars. `HomogeneousVectorBundle.cohomology`
  extends this to integer indices and is the actual zero module `Fin 0 → F` for
  negative indices. Negative vanishing is definitional, not an omitted theorem case.

Conclusions, clause by clause:

- The existential quotient and `D`, followed by finite local freeness, assert existence
  of all homogeneous bundles simultaneously, with their maps and left actions.
- The shared family `c M i` is counital and coassociative using `HopfAction` predicates.
  `IsNaturalCoaction D M i (c M i)` pins it by actual inverse-action pullback on sheaf
  cohomology and the given linearization. It cannot be replaced by a trivial coaction.
  The normalization is the universal-element tensor identity and therefore determines
  evaluation on every F-algebra, not only algebraically closed field points.
- `Module.Finite F (HOver ...)` is finite-dimensionality, and
  `Φ.card < i → Subsingleton (HOver ...)` is vanishing for i>N.
- For any representation map, `l` is explicitly equal to the existing `H.map`, and its
  tensor equation is S-equivariance. For a short exact module sequence the three
  hypotheses are injective, exact and surjective. The theorem asserts the induced
  sheaf short exact sequence, injectivity at H^0, and for every i the actual
  `H.δ hE i` as an F-linear map. Its coaction equation gives equivariance, and the
  three `Function.Exact` clauses give exactness at H^i(M2), H^i(M3), H^(i+1)(M1).
  Together with the negative-zero convention, these are the entire long exact sequence.
- `Nonempty (Filtration M)` states existence of a finite full flag. Its steps are
  actual stable subspaces; the successive factors are surjective character maps with
  exactly the preceding step as kernel. The theorem quantifies over every such flag.
- For each factor, the unipotent identity above and the nonzero vector v with
  `(coordinateMap jm).toLinearMap.lTensor _ (M.coaction v) = v ⊗ characterElement ...`
  give exactly a T-weight of M, not just a weight of a chosen abstract quotient.
- For every i and every simple V occurring as a coaction subquotient of H^i(M),
  the final filtration clause supplies some factor j with V a subquotient of H^i(F_xj).
  The finite representation binder loses no simple constituents: a subquotient of the
  finite-dimensional cohomology space is finite-dimensional.
- For every Borel character χ, ψ is explicitly its inverse as a group-scheme map.
  `e` is an F-linear equivalence from actual H^0 to the existing
  `RhoSection.sectionModule S Bm im ψ 1`. This subspace is exactly the regular functions
  with f(gb)=χ(b)^(-1)f(g), quantified over all commutative F-algebras. The value formula
  for e uses pullback of the actual section through π and D's fixed coordinates, then
  tensor contraction. Its tensor identity with `regularLeftCoaction` gives equivariance
  for the actual regular left action. `HasRationalLeftTranslation` records that same
  function-space action in the existing section-module interface.
- `topologicalKrullDim Q.left = (Φ.card : WithBot ℕ∞)` is dim(S/Bm)=N.

Dependency declarations read and reused:

- Mathlib `Field`, `IsAlgClosed`, and `CategoryTheory.GrpObj`, from their recorded
  mathlib matches; `Grp (Over (Spec F))` supplies the recorded group-scheme convention.
- `Sheaf.AlgebraicGeometry.RhoSectionModules`:
  `AlgebraicGeometry.IsRhoBorelPair`, `exists_rho_section_modules`; its precise
  semisimple/simply-connected interfaces were read, including the full signature.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `reductive_borel_pair_structure`, `semisimpleGroupScheme_isReductive`, and the recorded
  Lie-weight/root conventions. The quotient torsor square is the same square as there.
- `Sheaf.AlgebraicGeometry.RationalRepresentationGZero`:
  `EquivariantCoherent.RationalModule`, `Representation`, `IsRepresentationMap`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `coordinateAlgebra`, `coordinateHopf`, `coordinateMap`, `characterElement`, `IsStable`,
  `IsSimple`. No separate rational-representation, stability or simplicity definition.
- `Sheaf.AlgebraicGeometry.RhoSectionModuleData`: `RhoSection.Coordinate`,
  `sectionModule`, `HasRationalLeftTranslation`.
- `Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle`:
  `pullTopSection`, `pullSection`, with their exact composition transports.
- `WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison`:
  `HOver`, `extendComparison`, `invImage`, `constIso`, `coeff`; `Cohomology.Defs`:
  `Scheme.Modules.H`, `H.map`, `H.zeroLinearEquiv`; `Cohomology.LongExact`: `H.δ`.
- The new definition modules' full declarations are listed in their node lean records.
  The main module also imports every already recorded proof-dependency module listed
  in its proof plan, privately, as required for the later proof stage.

Source check: Andersen's GDZ IIIF manifest PPN243919689_0315 and scans 59--62 were
read visually (printed pp.55--58). Page 55 fixes inverse semi-invariance and inverse
left translation; p.56 supplies exact cohomology sequences; pp.57--58 use full Borel
filtrations and the dimension bound. Milne's locally available Algebraic Groups,
printed pp.468--471 and 479--480 (22.21, 22.29--22.30, 22.48), was read for the same
conventions. Source excerpts and downloaded scans are scratchpad material only.

Edge cases checked: the zero module admits length zero and no character factors;
then the simple-constituent claim is vacuous, as `IsSimple` requires nontriviality.
Steps after the length are forced to be top by monotonicity and the endpoint.
The empty positive-root set gives dimension zero and vanishing in every positive
degree, without assuming a positive rank. A character module is one-dimensional even
for the trivial character. Degree zero is connected to actual global sections, not
an unnamed isomorphic vector space. Negative cohomology is zero by construction.
Arbitrary schemes and coefficient algebras use the base universe u, never a separately
smaller test universe. The two existing coordinate scalar structures are bridged by
actual appTop and a uniquely determined linear inverse, not identified by an extra
hypothesis or by changing the Hopf algebra.

Searches: `msearch.py leanfinder` on "finite dimensional rational cohomology homogeneous
bundle flag variety Borel character filtration" found group/continuous cohomology,
not this result. `loogle "Coalgebra.Comodule, CategoryTheory.ShortComplex, Module.Finite"`
reported no Coalgebra.Comodule match; `loogle "Coalgebra, ModuleCat, ShortComplex"`
returned zero hits with unknown identifier `ShortComplex`; neither was treated as a successful match. Mathlib grep "homogeneous|Borel|flag variety"
in AlgebraicGeometry found polynomial homogeneity only. LeanSearch on "homogeneous
vector bundle on flag variety cohomology rational representations" found topological
bundles and continuous cohomology. Additional new-node searches are recorded verbatim
by query in their mathlib_searches. `rg` in WeilConjectures and Sheaf for the item id
and candidate declaration names found no existing statement; the related existing
components listed above were reused. DAG text searches found this item and related
proof lemmas, not another definition of the bundle system or character filtration.
Blueprint searches for "homogeneous vector bundle" and "character filtration" both
returned zero nodes. Ordinary `Representation.IsConstituent` is for abstract group
representations and does not encode coordinate coactions, so is not substituted.

No STATEMENT-DISPUTED flag or statement correction. Compile development found and
repaired a universe default in finite local freeness and the existing difference
between Hopf-coordinate and algΓ scalar encodings. All three files compiled using
scompile.py; final delivery validation is recorded below.

## New nodes

`def-sfb-rational-character-filtration`: introduces coaction subquotients, the actual
character module on F, and finite character flags with actual quotient maps. Sources
are Andersen pp.55--58 and Milne Sections 4a--4b, 22.29--22.30. LeanSearch and LeanFinder
for finite character filtrations returned generic module/ideal filtrations;
Mathlib RepresentationTheory grep found no character-coaction filtration. Project and
DAG searches found no owning definition node. The pre-existing stability, simplicity,
coordinate algebra and rational-module definitions are imported rather than copied.
Counit and coassociativity proof obligations are named helpers with full proof docstrings.

`def-sfb-homogeneous-vector-bundle`: introduces the coordinate descent presentation,
canonical scheme-point action, pullback and inverse-action maps, cohomology indexing,
and normalization of the natural coaction. It neither assumes local freeness nor
supplies arbitrary representations of cohomology. Sources are Andersen pp.55--56,
Milne Sections 18c and 22.29--22.30, 22.48, and the canonical sheaf-cohomology pullback
construction. LeanSearch/LeanFinder for an associated homogeneous vector bundle and
Mathlib AlgebraicGeometry grep returned presentations or topological bundles, not
this definition. Existing character-line-bundle pullbacks and the published Ext
cohomology are reused. Scalar compatibility is a named proof obligation; the only
inverse chosen is uniquely fixed by the identity coordinate map's bijectivity.

## Second reading by N0

The dispatcher explicitly prohibited starting other agents. This is a separate
self-review pass, not an independent second worker's review; the maintainer's
independent review remains required. I reread the original node beside all three
modules and both new nodes. I checked in particular the inverse character in H^0,
actual cohomology and its scalar structure, the normalization excluding arbitrary
coactions, canonical connecting maps, every filtration rather than a selected one,
the lift of quotient weights to weights in M, and the rank-zero/degree-zero cases.
The universe default and tensor-right-unit argument found during compilation were
repaired. No mathematical statement mismatch was found. The Borel-character encoding
is documented above; unused Weyl-group context creates no assumptions. The new node
records list all helpers and postpone only their proof fields. All definitions have
explicit data and all theorem proofs are sorry-only.

Final validation: `deliver2.py N0 lem-sfb-flag-cohomology-finite-exact --no-push`
reported OK: the full packet passes server preflight and every module compiles
without errors or unexpected warnings. All compiles used the prescribed scompile
wrapper and its published-live-library overlay; no global build was run.
