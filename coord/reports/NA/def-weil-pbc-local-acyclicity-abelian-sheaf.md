## Worker report

The module `Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf` defines the canonical
strict-local map, its geometric fibres, the canonical alpha homomorphism, local acyclicity
at a point relative to an abelian sheaf, local acyclicity relative to that sheaf, local
acyclicity without specified coefficients, and universal local acyclicity. Nothing is
proved. The only `sorry` is the named theorem
`AlgebraicGeometry.Etale.existsUnique_localAcyclicityStrictMap`, whose docstring gives the
limit construction and uniqueness argument. The map chosen from that theorem is uniquely
determined by its equations; no object is chosen from an undetermined existence statement.

Clause-by-clause correspondence:

- Schemes and their morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- An abelian sheaf is `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X)`; its image is `x ≫ f`.
- The strict local schemes are `Scheme.strictHenselizationScheme x` and
  `Scheme.strictHenselizationScheme (x ≫ f)` from the recorded limit dependency.
  Their maps to the original schemes are `Scheme.strictHenselizationStructuralMap`.
- `localAcyclicityStrictMap` is the unique map commuting with those structural maps
  and carrying the distinguished geometric point to the distinguished geometric point.
  These equations characterize the map of pointed-neighbourhood limits in clauses (3)-(4)
  of the functoriality dependency. Uniqueness follows by pointed étale rigidity on each leg.
- The test point is `(Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
  (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme (x ≫ f))`.
  It has no algebraicity hypothesis.
- `localAcyclicityFiber f x t` is exactly `pullback (localAcyclicityStrictMap f x) t`.
  Its map to X is `pullback.fst _ t ≫ Scheme.strictHenselizationStructuralMap x`.
- Inverse images are `Etale.upperStar AddCommGrpCat.{u + 1}` throughout.
- `localAcyclicityAlpha` starts with the unique map characterized by
  `existsUnique_strictHenselizationStalkRestriction x G`. This is the inverse of the
  strict-local germ isomorphism, not an arbitrary isomorphism between the two groups:
  its defining equations prescribe its composite with every pointed-neighbourhood germ.
  The proof of this identification is also recorded in the existing
  `Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso` module. The next factor is
  `globalSectionsUpperStarMap` along the first fibre projection, followed by the inverse
  of `upperStarComp` on global sections. Thus its codomain uses exactly the pullback
  of G along the displayed composite to X. Degree zero is expressed as global sections.
- `IsLocallyAcyclicAtRelative` quantifies over all the test points, requires
  `IsIso (localAcyclicityAlpha f x t G)`, and for every natural `q` with `0 < q` requires
  `IsZero ((cohomology ... (q : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj ...))`.
  This uses the dependency's derived-functor cohomology on the sheaf in degree zero.
- `IsLocallyAcyclicRelative` universally quantifies over geometric points x.
- `IsLocallyAcyclic` universally quantifies over x and positive `n : ℕ`. The characteristic
  clause is `ringChar (X.residueField (x default)) = 0 ∨
  n.Coprime (ringChar (X.residueField (x default)))`. Thus characteristic zero allows
  every positive n. The coefficients are the recorded `constantSheaf` applied to
  `AddCommGrpCat.of (ULift.{u + 1} (ZMod n))`; ULift changes only the universe.
- `IsUniversallyLocallyAcyclic` quantifies over every `S' : Scheme.{u}` and every
  `g : S' ⟶ S`, applying local acyclicity to `pullback.snd f g`.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`.
- Mathlib.CategoryTheory.Sites.Sheaf and Mathlib.AlgebraicGeometry.Sites.Etale:
  `Sheaf`, `Scheme.smallEtaleTopology`.
- Mathlib.FieldTheory.IsAlgClosed.Basic and Mathlib.AlgebraicGeometry.ResidueField:
  `IsAlgClosed`, `Scheme.SpecToEquivOfField`, `Scheme.residueField`.
- Sheaf.AlgebraicGeometry.StrictHenselization: `Scheme.strictHenselizationRing`,
  `Scheme.strictHenselizationScheme`, and the limit cone/properties.
- Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap:
  `Scheme.strictHenselizationStructuralMap` and its characterizing existence theorem.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.fst`,
  `pullback.snd`.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs:
  `Etale.upperStar`, `Etale.upperStarComp`, `Etale.upperStarLowerStarAdjunction`.
- Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk:
  `Scheme.strictlyHenselianSections_geometricStalk_isIso`.
- Sheaf.Paper.InverseImageStalkGerm: `inverseImage_stalk_germ`.
- Mathlib.CategoryTheory.Sites.Point.Basic and Mathlib.AlgebraicGeometry.Sites.EtalePoint:
  `Point.sheafFiber`, `Scheme.pointSmallEtale`.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  `Etale.cohomology`, `Etale.rightDerivedGlobalSections`.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `constantSheaf`.
- Sheaf.Paper.StrictHenselizationFunctoriality:
  `strictHenselizationResidue`, `strictHenselizationFunctoriality`.
- Already landed nodes added to stmt_deps: def-weil-pbc-strict-henselization-point-evaluation
  (`Sheaf.Paper.StrictHenselizationPointEvaluation`,
  `Scheme.strictHenselizationPointEvaluation`) and
  def-weil-pbc-strict-henselization-restriction
  (`Sheaf.AlgebraicGeometry.StrictHenselizationRestriction`,
  `Etale.existsUnique_strictHenselizationStalkRestriction`). These existing canonical
  constructions avoid duplicating the evaluation map and stalk-to-sections restriction.

Edge cases: the empty source has no geometric points and the predicates are vacuous;
the zero sheaf gives zero stalk and zero cohomology and an isomorphism between zero groups.
An empty vanishing-cycle fibre is retained, so nonzero stalks can make local acyclicity fail.
Degree zero is treated by alpha, positive degrees by the explicit q inequality; negative
degrees of a sheaf in degree zero are not extra conditions. n = 0 is excluded, n = 1 is
allowed, all positive n are allowed in characteristic zero, and multiples of a positive
residue characteristic are excluded. No finiteness, separateness, smoothness, or algebraic
geometric-point restriction is added. All schemes and fields use a common arbitrary
universe u, with abelian sheaf values in u+1, as in the dependency interfaces.

Searches (2026-10-15): msearch.py leanfinder query "Local acyclicity of a morphism relative
to abelian etale sheaves using strict henselizations" returned eight unrelated étale
morphism/site hits; none states this notion. msearch.py loogle query
"IsLocallyAcyclic, locallyAcyclic" returned zero hits (unknown identifier IsLocallyAcyclic).
msearch.py grep query "locally.?[Aa]cyclic|[Ll]ocalAcyclic" returned zero hits. Direct rg of
the pinned WeilConjectures source and lean/Sheaf for the same concept found only an unrelated
AffineLocalAcyclicOpenRestriction import. Direct search for the item id and proposed full
names in upstream/project sources and dag/lean_names_upstream.json found no declaration.
A read-only search of live source also found no local-acyclicity definition. The canonical
stalk restriction and point evaluation were found by source search and reused.

Source checked: literature/stacks-project/etale-cohomology.tex, section Local acyclicity,
equation-alpha-K, definition-locally-acyclic, and following degree-zero description. The node
is unchanged mathematically. No STATEMENT-DISPUTED and no new nodes.

Validation: the delivered module compiled cleanly with scompile.py on the server,
nice 19, two threads, 60 seconds per file (3.7 seconds). No local Lean invocation.

## Dependency modules

`def-weil-pbc-strict-henselization-structural-map`: the recorded upstream
`Scheme.strictLocalizationToBase` has domain `Scheme.strictLocalization`, while the limit
node records the separate project construction `Scheme.strictHenselizationScheme`. These
are not definitionally the same. The existing project module
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` supplies exactly the structural
map on that recorded construction, characterized by all its affine representative legs.
Its full source and docstring were read. The dependency record is corrected to reuse that
existing declaration; no module is copied or introduced. Both upstream and project imports
were checked on the server; this is an interface mismatch, not a missing artifact.

## Second reading by NA

Independent reading against the node and etale-cohomology.tex, section Local acyclicity,
Tag 0GJP, equation-alpha-K, definition-locally-acyclic and its following cohomology
paragraph. The section assumes arbitrary schemes and morphisms; it adds no Noetherian,
finite-type, separatedness, or smoothness assumption. The node intentionally gives the
abelian-sheaf-in-degree-zero specialization and includes source clauses (1), (2), (4),
and (5); source clause (3), universal relative acyclicity, is not claimed by this node.
The node has no statement_change, and its mathematical statement is retained.

Object/hypothesis/conclusion checklist, in the node's order:

- Arbitrary schemes X, S and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  Verdict: exact, with no extra geometric-property instance.
- Abelian sheaf G on the small etale site: `Sheaf X.smallEtaleTopology
  AddCommGrpCat.{u + 1}`. Verdict: the recorded sheaf and site, not module coefficients
  or a big-site replacement.
- Algebraically closed geometric point x and its image s: `{Ω : Type u} [Field Ω]
  [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)` and `x ≫ f`. Verdict: exact; no algebraicity
  condition on Ω is introduced.
- Strict henselizations and their structural maps: `Scheme.strictHenselizationScheme`
  and `Scheme.strictHenselizationStructuralMap` at x and x ≫ f. Verdict: these use the
  coordinate-ring colimit and its limit legs of the recorded dependency, read in
  StrictHenselization.lean and StrictHenselizationStructuralMap.lean.
- Canonical induced strict-local morphism: `existsUnique_localAcyclicityStrictMap`
  prescribes the structural square and compatibility with the distinguished Spec Ω
  points constructed by `Scheme.strictHenselizationPointEvaluation`.
  `localAcyclicityStrictMap` chooses that unique map. Verdict: equivalent to the
  pointed-neighbourhood-induced morphism, not an arbitrary morphism. The evaluation
  source was opened: it is colimit.desc of the actual pointed evaluation cocone.
  The two displayed equations impose the same residue compatibility as clauses (3)-(4)
  of strictHenselizationFunctoriality; pointed etale rigidity determines each limit leg.
- Every geometric test point t, with no algebraicity restriction: `∀ (Ω' : Type u)
  [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ ... )`. Verdict: exact. There is
  no finite-extension or residue-algebraicity binder.
- Vanishing-cycles fibre and its map to X: `localAcyclicityFiber f x t` is
  `pullback (localAcyclicityStrictMap f x) t`; its composite to X is `pullback.fst ... ≫
  Scheme.strictHenselizationStructuralMap x`. Verdict: correct fibre and projection.
- Inverse-image coefficients: `upperStar AddCommGrpCat.{u + 1}` along that composite.
  Verdict: the recorded inverse image, whose adjunction signature and construction
  in UpperLowerStar.Defs were opened.
- Stalk and canonical degree-zero alpha: `(Scheme.pointSmallEtale x).sheafFiber.obj G`
  to `Sheaf.Γ` on the fibre, implemented by `localAcyclicityAlpha`. Verdict: exact.
  I read `IsStrictHenselizationStalkRestriction` and its existence/uniqueness theorem:
  each germ component is the inverse-image unit followed by restriction along the
  actual limit leg. This identifies the chosen map, rather than merely specifying
  an isomorphism of its endpoints. I also opened StrictLocalGermRestrictionIso.lean,
  which identifies precisely this restriction with the inverse of the germ
  isomorphism. `globalSectionsUpperStarMap` then restricts to the fibre and
  `upperStarComp.inv` puts its coefficients on the specified composite to X.
- Relative local acyclicity at x: `IsLocallyAcyclicAtRelative` requires alpha to be
  `IsIso` and `∀ q : ℕ, 0 < q → IsZero (...)`. Verdict: both clauses, for each t,
  in the correct quantifier order. `cohomology` was opened in Derived.LowerShriek:
  it is right derived global sections followed by degree-q homology, applied here
  to `DerivedCategory.singleFunctor _ 0` of the inverse-image sheaf.
- Relative local acyclicity everywhere: `IsLocallyAcyclicRelative` quantifies over
  all Ω and x and applies the preceding predicate to the same G. Verdict: exact.
- Unqualified local acyclicity: `IsLocallyAcyclic` quantifies over x and positive
  `n : ℕ`, with `ringChar ... = 0 ∨ n.Coprime (ringChar ...)`, and uses
  `(constantSheaf ...).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))`.
  Verdict: exact; the residue field is at `x default`, the unique source point.
  I opened residueField and constantSheaf: the former is the local-ring residue
  field, the latter is sheafification of the constant presheaf. ULift only changes
  the group carrier's universe.
- Universal local acyclicity: `IsUniversallyLocallyAcyclic` quantifies over S' and
  g and tests `IsLocallyAcyclic (pullback.snd f g)`. Verdict: exactly the base-changed
  morphism to S', not the projection to X.

Dependency-record reading: the delivered structural-map node changes only lean.
Its reused project declaration has domain `strictHenselizationScheme s` and is the
common composite of the specified representative limit legs to S, exactly as its node
and Tag 03Q9 require. It is already present in lean/Sheaf; no dependency module or new
node is introduced. The old upstream record names `strictLocalizationToBase`, for a
separate construction. Reusing the existing project map is appropriate for the recorded
limit dependency. I read all dependency node statements and records, and the signatures
of the stalk, inverse-image, cohomology, constant-sheaf, residue-field, strict-limit,
structural-map, point-evaluation and germ-restriction declarations actually used.

Edge cases: empty X makes the pointwise predicates vacuous; an empty test fibre is
retained and requires the stalk-to-zero alpha to be an isomorphism. For the zero sheaf
the stalk and cohomology conditions have the expected zero objects. There is no index
family whose empty case is accidentally excluded. q = 0 is handled by alpha and only
q > 0 is required to vanish. n = 0 is excluded by the node, n = 1 is included. In
characteristic zero every positive n is admitted; in characteristic p only coprime n
are admitted. u is arbitrary, shared by schemes and geometric-point fields as in the
recorded dependencies; abelian values are in u+1. No independent smaller test universe,
finite field, or algebraic geometric-point restriction appears. All binders are explicit.

Independent searches (2026-10-15): LeanFinder through msearch.py, query "Vanishing cycles
fibres identify sheaf geometric stalks with global sections and higher etale cohomology
vanishes", returned eight unrelated stalk/skyscraper results. Loogle through msearch.py,
query `"acyclic"`, returned complex acyclicity and metaprogramming declarations, not local
acyclicity of scheme morphisms. Direct case-insensitive rg for
`vanishing.?cycles|locally.?acyclic|local.?acyclicity` across Mathlib, the pinned upstream
WeilConjectures tree and the project's lean/Sheaf found only AffineLocalAcyclicOpenRestriction
and FiniteAffineCoverRestrictionBound in the project. I opened the former: its hypothesis
is vanishing on inverse images of affine opens, a different notion, not this definition.
No existing local-acyclicity declaration was found. The existing canonical restriction
and point evaluation are reused, as required by H4.

No mathematical or Lean mismatch was found; no Lean or node changes were necessary.
The sole new theorem has a named sorry, a source and stepwise natural-language proof;
all definitions have actual constructions or uniquely specified data, with no embedded
sorry. The node's lean.statement agrees verbatim with the normalized declaration
signature. This second reading adds this report only. The delivered Lean module compiled
cleanly via scompile.py on the server in 3.6 seconds, nice 19, two threads, 60-second limit.
