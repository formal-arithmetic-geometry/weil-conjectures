## Worker report

The module states the strict-henselization stalk comparison for the multiplicative étale sheaf. It binds a qcqs morphism `f : X ⟶ S`, an algebraically closed geometric point `xbar`, an explicit map `g : S_(xbar) ⟶ S`, and `q : ℕ`; the left side is the `q`th homology sheaf-fiber of the derived direct image and the right side is étale cohomology on the strict-henselization scheme after étale pullback of `𝔾ₘ`. The proof is `sorry` as required for stage 2.

The dependencies used are `Sheaf.AlgebraicGeometry.StrictHenselization` (`AlgebraicGeometry.Scheme.strictHenselizationScheme` and related declarations), `WeilConjectures.AlgebraicGeometry.Sites.Gm` (`AlgebraicGeometry.Scheme.gmSheaf`), `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` (`AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`), and `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` (`AlgebraicGeometry.Etale.cohomology`). `Scheme.pointSmallEtale` renders geometric stalks; `Etale.upperStar` renders inverse image.

Edge cases checked: `q = 0` is admitted by the natural-number binder; no nonemptiness, properness, or characteristic hypothesis is added; universes use the scheme universe for the geometric point and coefficient category.

Searches made: `msearch.py` LeanSearch query “higher direct image stalk of multiplicative sheaf strict henselization” (service unavailable); LeanFinder query “higher direct image stalk equals etale cohomology over strict henselization for units sheaf” (no matching declaration); grep query `strictHenselization|stalkPushforward|gmSheaf` (found only generic stalk-pushforward and `gmSheaf` declarations). Upstream grep found no complete strict-henselization formula.

Resolved concern from the initial draft: the dependency definition supplies no canonical morphism `S_(xbar) ⟶ S`; the Lean statement therefore exposes this morphism as an explicit parameter `g`, while retaining the source's comparison shape. This is recorded so the second reader can decide whether a canonical map definition node is required.

## Dependency modules

`def-weil-pbc-strict-henselization-limit`: the initial draft copied its module because an
object file was unavailable. The second reading found the original import now compiles and
rejected that cache-based reason. The delivered extension instead repairs the actual missing
canonical maps: the spectrum cone is transported to the original affine neighbourhoods,
extended to all pointed neighbourhoods using its already-stated initiality, and evaluated at
`(S,xbar)` to obtain `Scheme.strictHenselizationToBase`. The original ring, scheme, cone,
small representatives and independence definitions are kept. Its `lean.note` explains this
mathematical need. New proof obligations are naturality of the transported legs and their
compatibility over the base; their source and full proofs are in the docstrings.

## Earlier second reading (a previous round; superseded)

Superseded by the completed independent second reading below; both issues were repaired.


## Second reading by Q1

Read the node and all its statement dependencies independently of the first draft. The
local literature checkout omits the cited Stacks files, so I obtained the official source
`https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex` in
`scratchpad/etale-cohomology.tex`, and read `theorem-higher-direct-images` (Tag 03Q9), the
preceding `lemma-directed-colimit-cohomology` (Tag 09YQ), and
`lemma-vanishing-etale-cohomology-strictly-henselian` (Tag 03QO). There are no standing
Noetherian, properness, torsion, finiteness, characteristic, or separated-scheme hypotheses
in 03Q9; its hypotheses are qcqs on the morphism and an abelian sheaf. The node is correct
and was not changed. Its units clause is the special pro-étale neighbourhood-limit
comparison, not the false assertion that arbitrary inverse image preserves G_m.

Object/hypothesis/conclusion checklist, matched item by item:

- Schemes X and S: `{X S : Scheme.{w}}`. Same objects and arbitrary scheme universe; pass.
- Morphism f: `(f : X ⟶ S)`. No over-field structure imposed; pass.
- Quasi-compact and quasi-separated morphism: `[QuasiCompact f] [QuasiSeparated f]`.
  These are the convention node's Mathlib properties of f, not properties of X or S; pass.
- Units sheaf on X: `X.gmSheaf` from the Gm source module, read in full. It is the additive
  abelian sheaf of units of Γ(U,O_U), with ULift only to adjust the coefficient universe.
  No coefficient field or torsion condition; pass.
- Geometric point: `{Ω : Type w} [Field Ω] [IsAlgClosed Ω]` and
  `(xbar : Spec (.of Ω) ⟶ S)`. This is the exact geometric-point node convention; pass.
- S_(xbar): `Scheme.strictHenselizationScheme xbar`, the recorded spectrum of the coordinate
  ring colimit. I read its small representative functor, affine pointed-category equivalence,
  coordinate ring diagram, spectrum cone, initiality/limit properties and representative
  independence signatures and definitions. Its index includes lifts, not just neighbourhood
  schemes. Its ring and scheme construction are retained; pass.
- Canonical map to S: `Scheme.strictHenselizationToBase xbar`, obtained from the extended
  cone at `(S,xbar)`. No arbitrary g or existence hypothesis occurs in the final theorem;
  pass after repair.
- Fibre product and projection p: `pullback f (Scheme.strictHenselizationToBase xbar)` and
  `pullback.fst f (Scheme.strictHenselizationToBase xbar)`. Mathlib's pullback/fst/snd
  signatures and the Scheme pullback instance give the precise objects in the node; pass.
- Every q >= 0: `(q : ℕ)`; the same q is coerced to ℤ throughout the derived homology and
  cohomology. No q > 0 restriction; pass.
- Left side: in `strictHenselizationStalkCohomologyMap`, `pointSmallEtale xbar`.sheafFiber
  applied to H^q of `rightDerivedLowerStarPlus ... f` applied to `singleFunctor ... 0`
  of `X.gmSheaf`. Read Point.sheafFiber and pointSmallEtale, lowerStar and upperStar,
  upperStarLowerStarAdjunction, and rightDerivedLowerStarPlus in their source modules.
  This is exactly `(R^q f_* G_m)_xbar`; pass.
- Right side with inverse-image coefficients: the map's codomain is `Etale.cohomology`
  on the fibre product, evaluated at Plus.ι of single 0 of `upperStar ... p` applied to
  `X.gmSheaf`. Read rightDerivedGlobalSections and cohomology and the dependency node's
  record. This is H^q(X',p^{-1}G_m), with the same coefficients and site; pass.
- The *canonical restriction map* is an isomorphism: first conjunct
  `IsIso (strictHenselizationStalkCohomologyMap xbar f X.gmSheaf q)`. The new definition
  constructs the map explicitly from neighbourhood restrictions, the stalk colimit,
  exact-inverse-image homology comparison, the derived base-change mate, exact global
  sections on the strict local base, and the source's canonical Leray isomorphism. It
  does not choose a map or an isomorphism from an existence theorem. Its degree-zero
  restriction is the unit followed by restriction along the canonical limit section.
  The derived mate is Mathlib `mateEquiv` applied to the existing pullback-square
  comparison and `(upperStarLowerStarAdjunction ...).derivedPlus`; this avoids imposing
  the monoidal hypotheses of the source's alternative `baseChange` API. Pass after repair.
- Canonical units comparison is an isomorphism: second conjunct
  `IsIso (Scheme.upperStarGmSheafToGmSheaf p)`. Read that existing definition: it is precisely
  the adjoint of `gmSheafToLowerStarGmSheaf`, whose components pull back units along the
  projection. It is not an arbitrary sheaf isomorphism; pass after repair.
- Final identification with cohomology of G_m on X': third conjunct asserts IsIso of
  the first comparison followed by `cohomology.map` of Plus.ι of singleFunctor.map of
  the canonical units map. Its source is the same stalk and its target is H^q(X',X'.gmSheaf).
  This is the canonical identification promised by the last clause; pass after repair.

Edge cases: X may be empty; no point or nonempty instance on X is bound. If S is empty,
the geometric-point parameter cannot exist, exactly as in the node. q = 0 gives the usual
units restriction map. The auxiliary construction works for the zero abelian sheaf too;
no injectivity/nonzero assumptions were introduced. There is no free index set in the
statement: the neighbourhood index is the dependency's SmallModel in the scheme universe,
so an empty or artificially smaller indexing universe was not added. Ω and schemes have
the same universe as in the recorded geometric-point/strict-henselization definitions;
ULift permits the abelian coefficient category in the next universe and introduces no
field-size or characteristic bound. Every universe and variable is explicitly declared
or section-bound; autoImplicit=false compilation checks this.

Independent H4 searches: ran msearch.py LeanFinder for "canonical restriction of geometric
germs to cohomology of a strict local base change" (only topological germs and a Tilde germ
formula), LeanSearch with the same query (service unavailable), Loogle for
`CategoryTheory.GrothendieckTopology.Point.sheafFiber` (generic stalk API only), and Mathlib
grep for `hensel.*cohomology|stalk.*restriction|stalk.*direct.*image` (only ringed-space
stalk restriction). Independently rg'd WeilConjectures and lean/Sheaf for strictHenselization,
strict/local germ restriction, higher direct images, Gm comparison, and the proposed names;
read the Gm, global-sections, derived-global-sections and base-change modules. The general
cohomology pullback, strictly henselian sections/stalk theorem, exact-global-sections/
acyclicity theorem and FibreProductNeighbourhoodLimit do not define this canonical
higher-direct-image stalk restriction. Searched the DAG with blueprint_refs.py search
"strict henselization" and rg across nodes: no definition node carries this map.
There is no complete existing theorem stating all three clauses, so this is not an
existing-declaration delivery. Queries and actual results are recorded in searches.jsonl.

Mismatches found and repaired: the draft used cohomology on S_(xbar), omitting X ×_S S_(xbar);
it pulled back S.gmSheaf instead of X.gmSheaf; it bound an arbitrary g; it asserted only
Nonempty of an unspecified isomorphism; it omitted the canonical units comparison; and
it omitted the final G_m-coefficient identification. Replaced the statement with the three
canonical IsIso assertions and added the necessary restriction-map definition node and
canonical-map extension of the existing strict-henselization dependency. The initial
STATEMENT-DISPUTED concern is resolved, not retained. No unit or mathematical node statement
was weakened or corrected. No new data definition contains sorry; named naturality and
exactness proof obligations have source/proof docstrings and the corresponding node.
Every theorem proof remains sorry, as stage 2 requires.

Compilation: all three delivery modules compile together, in dependency order, under the
server's default timeout and options, with no errors or warnings. The node lean.statement
records are extracted verbatim from their respective source signatures. The delivery
preflight also required individual bracketed citations in the new definition node and
the current complete blueprint ancestry path; both metadata points were repaired.

## New nodes

`def-weil-pbc-strict-henselization-restriction` introduces the specific restriction map from
higher-direct-image stalks to cohomology on the strict-local base change. Its source is the
construction in Stacks 03Q9 and exactness on the strict local base in 03QO. The statement
spells out the germ restriction, neighbourhood-section formula, compatibility needed for
colimit descent, derived mate, and canonical Leray comparison. Its module uses the existing
stalk, direct image, inverse image, cohomology, derived adjunction and Leray constructions,
not private copies. It defines maps for every f without assuming they are isomorphisms.
Searches of the DAG, Mathlib, WeilConjectures and lean/Sheaf, and the independent service
queries above, found no existing definition of this map. The named exactness obligation
specializes 03QO to the already-defined strict henselization; the generic ring acyclicity
and sections/stalk nodes remain shared and are not redefined.

## Reviewer fix (R-gsf)

- `Scheme.strictHenselizationToBase` and the extended neighbourhood cone added to
  `StrictHenselization.lean` were a second spelling of the landed
  `Scheme.strictHenselizationStructuralMap` (def-weil-pbc-strict-henselization-structural-map,
  14067f949), and the extension chose data through the sorried initiality (H4/H5): the change to
  def-weil-pbc-strict-henselization-limit and its module is reverted; both modules use the landed
  structural map and `strictHenselizationCone`.
- The germ restriction `r_G` was built by descending maps over all pointed neighbourhoods through
  that chosen cone. It is now characterised: `IsStrictHenselizationStalkRestriction s G r`
  (components at the representative affine neighbourhoods) with
  `existsUnique_strictHenselizationStalkRestriction`; the derived-mate/Leray part is the
  definition `strictHenselizationCohomologyComparison`, so rho^q = r ≫ comparison.
- The item states `∃ r, IsStrictHenselizationStalkRestriction … r ∧ IsIso (r ≫ comparison) ∧
  IsIso (upperStarGmSheafToGmSheaf p) ∧ IsIso (r ≫ comparison ≫ H^q(units map))`, r tied by the
  uniqueness theorem.
