## Worker report

The module `Sheaf.AlgebraicGeometry.OpenSheafCoproductBaseChange` states
`AlgebraicGeometry.Scheme.openSheafCoproduct_baseChange` with one postponed proof.
The natural-language statement is unchanged. Its proof docstring follows all seven
DAG steps, including construction of both directions, inverse identities, naturality,
test change, and the empty-index case. The auxiliary structure and predicate have
actual data/defining expressions; neither uses `sorry`. No other theorem is introduced.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. Site objects are `Over S`; the site is
  `fppfTopology.over S`. All variables and universes are explicitly bound.
- The size convention is implemented with scheme universe `u` and coefficient/index
  universe `max u v`. `uliftYoneda.{v}.obj X` has exactly the canonical lifted sets
  `Mor_S(W,X)`, with restriction by composition. Neither universe is identified with
  the other, and the scheme universe is not enlarged to the section universe.
- The sheaves `F`, `Fi`, and `H` are `Sheaf (fppfTopology.over S) (Type (max u v))`.
  The family is indexed by `I : Type (max u v)`, allowing any small index in that bound.
- `ι : ∀ i, Fi i ⟶ F` with `hmono : ∀ i, Mono (ι i)` expresses subfunctor inclusions.
  A monomorphism of set-valued sheaves is exactly an inclusion up to its canonical
  isomorphism onto its subfunctor image. The sectionwise subset notion is the existing
  `CategoryTheory.Subfunctor`; a second subset notion is not defined here.
- `hopen` uses the universe-general helper predicate
  `AlgebraicSpace.IsRepresentableWithLift (fun _ _ p ↦ IsOpenImmersion p.left)`.
  It quantifies over all scheme tests and supplies an open scheme projection and its
  representing cartesian square, exactly representability by open immersions.
- `j` and `hcol : IsColimit (Cofan.mk H j)` mean the given coproduct in sheaves with
  its specified injections. `q` and `hfac : ∀ i, j i ≫ q = ι i` give its specified map.
- A test is `T : Over S`, `t : uliftYoneda.obj T ⟶ F.obj`. The helper record
  `OpenSheafCoproductTest Fi ι T t` packages the choices the node introduces: `V i`,
  `inclusion i`, `sectionMap i`, their `cartesian` squares and `isOpen` projections;
  `C`, `injection`, and `isColimit` are the scheme coproduct, using the universal
  property in schemes themselves, not merely a sheaf or relative coproduct.
  `p` with `injection_p` is its uniquely induced scheme morphism into `T`.
- `hsite` says these data can be chosen for every test within the chosen scheme
  universe. This renders the node's explicit assumption that the scheme coproduct
  lies in the chosen big site. The other fields are already supplied by `hopen` and
  the coproduct universal property; the assumption adds exactly the site-size bound.
  In particular it does not claim that an arbitrarily large index set always has its
  scheme coproduct in `Scheme.{u}`. The conclusion applies to EVERY choice `D` of
  the specified representing opens and coproduct, not just to an existential choice.
- The first conclusion is `∀ X, Presheaf.IsSheaf ... (uliftYoneda.obj X)`:
  all the representable test functors are fppf sheaves.
- `∃! e : uliftYoneda.obj D.C ≅ pullback q.hom t, ...` is the canonical isomorphism
  `h_C ≅ H ×_F h_T`. Its target is the presheaf pullback of sheaves and hence a sheaf;
  full faithfulness of the sheaf inclusion identifies this with the sheaf isomorphism.
- `D.ComparisonEquations j q e` states BOTH specified equations: on every summand
  the H-projection is `D.sectionMap i ≫ (j i).hom`, and the T-projection on the whole
  source is `uliftYoneda.map D.p`. Composing the latter with a summand injection
  gives the other projection of the specified summand map, by `D.injection_p`.
- Test compatibility quantifies over every `T'`, `f : T' ⟶ T`, and every new set of
  choices `D'` for `uliftYoneda.map f ≫ t`. The unique `di` is characterized by its
  universal-section and test-projection equations. The unique `d` restricts to
  these `di` on the coproduct summands. Thus these are the canonical induced maps,
  rather than unconstrained arrows or an arbitrarily chosen comparison.
- `d ≫ D.p = D'.p ≫ f` is compatibility over the tests.
  `IsPullback d.left D'.p.left D.p.left f.left` identifies the new scheme coproduct
  with the scheme base change. The final two equations assert compatibility with
  every new comparison `e'` having the specified equations, after both pullback
  projections. Together these are exactly the naturality square for the isomorphisms.
- `AlgebraicSpace.IsRepresentableLift q.hom` gives the in-particular representability
  assertion for every scheme test. The projection equation identifies its scheme
  base change with the stipulated morphism `C_T → T`.
- No union-of-opens/covering assumption, `Epi q`, or algebraic-space hypothesis on
  `F`, `Fi`, or `H` is imposed. None is hidden in either helper record.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`, `fppfPrecoverage_le_fpqcPrecoverage`, fpqc subcanonicity,
  `zariskiPrecoverage_le_fppfPrecoverage`. These supply the recorded fppf/fpqc descent
  and covering-comparison proof inputs as well as the statement's site.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings` and its
  retained Mathlib `Sheaf` convention; no second definition of sheaf/site is used.
- `Mathlib.CategoryTheory.Subfunctor.Basic`: `Subfunctor`, read with its restriction
  stability field; inclusions are expressed by the equivalent monic interface above.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace.IsRepresentableWith`,
  `IsRepresentable`, read in full, and their universe-general helper interface in this item module.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.HasLimits` / `IsLimit`: `colimit`, `Cocone`,
  `IsColimit`; `Cofan.mk` packages the discrete-diagram coproducts.
- `Mathlib.AlgebraicGeometry.Limits`: scheme coproduct existence, `sigmaOpenCover`,
  `disjoint_opensRange_sigmaι`, with their `Small.{u}` hypotheses read. Explicit
  scheme cofans allow the node's stated site-size assumption without adding a
  uniform Small.{u} hypothesis on the whole index set.
- `Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition` is a plain proof import;
  `Scheme.fppfSheaf_coproduct_partition` is the recorded partition/gluing input.
- `Mathlib.CategoryTheory.Yoneda`: `uliftYoneda`, `uliftYonedaIsoYoneda`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`: `IsPullback`.

The exact source sentence was read in `literature/stacks-project/spaces.tex`,
lemma-glueing-algebraic-spaces (Tag 02WR), first proof paragraph. It uses only the
representable-open hypotheses to identify the fibre product with the scheme coproduct;
the later covering and algebraic-space hypotheses are not needed for this sentence.

Edge cases checked before and after drafting: empty index (the initial sheaf has one
section on an empty test, not the pointwise empty presheaf); empty summands; empty
`T` and `S`; two identical open subfunctors (the two summands remain distinct);
a union properly contained in `T` (the projection need not be surjective); infinite
index; larger coefficient/index universe with coproduct explicitly assumed in the
site; identity and arbitrary nonflat test changes; different choices of representatives
and coproducts. None requires an additional hypothesis or a statement correction.

Searches for an existing statement (all on 2026-10-22):

- `msearch.py`, LeanFinder: "Base change of a coproduct of fppf sheaves represented by
  open immersions is represented by the disjoint union of the scheme pullbacks".
  Eight hits: scheme coproduct section rings, open-immersion sigma descents, binary
  scheme pullback squares, disjoint scheme coproducts, finite extensivity and relative
  scheme coproduct existence. None states the relative sheaf comparison.
- `msearch.py`, Loogle: `"IsPullback", "coproduct"`. Two hits,
  `CoproductDisjoint.isPullback_of_isInitial` and `FormalCoproduct.isPullback`;
  neither is this statement or the relative scheme-test predicate.
- `msearch.py`, grep in Mathlib AlgebraicGeometry:
  `IsRepresentable|coproduct.*sheaf|sheaf.*coproduct`. Nine hits: subcanonical
  representables and local scheme representability; no match for this statement.
- `msearch.py`, LeanSearch: "A coproduct of fppf sheaves whose summands are open
  subfunctors has pullbacks represented by scheme coproducts". Eight hits: locally
  ringed space coproducts, binary scheme pullbacks, coproduct section rings, affine
  morphism coproducts and open-immersion pullbacks. No matching sheaf comparison.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `IsRepresentableWith|IsRepresentable.*[Uu]niverse|open.*[Ss]heaf.*[Cc]oprod|[Cc]oprod.*[Bb]ase[Cc]hange`:
  the existing algebraic-space predicate and consumers, and unrelated finite constant
  étale coproduct/base-change results. The open-gluing theorem assumes the summands
  and coproduct are algebraic spaces and concludes that F is an algebraic space;
  it does not supply this lemma. `grep -rn` for this node id in WeilConjectures
  returned no occurrence. A final `rg` for all new declaration names in Mathlib,
  WeilConjectures and Sheaf returned no collision.

Validation before return: `scompile.py` compiled the original two-file packet
without errors or unexpected warnings. The repaired one-file packet is validated below. No direct compilation, library write, global build or git
command was run in the read-only checkout. No STATEMENT-DISPUTED issue remains.

## Repair of returned H13

The returned immutable head was `62f959c2e2e8`. The initial dry run of the saved
packet passed as commit `25f888d84e2`, but that mechanical success did not repair
the independent review's H13 finding. The dependency record had been rebound from
Q128's full algebraic-space interface to just two representability predicates.

The sandbox copy of `def-trf-algebraic-space.json` is now byte-identical to the
live repository copy: its module, primary declaration, statement, author and all
21 declaration names are preserved. The original module is imported directly.
`IsRepresentableWithLift` and `IsRepresentableLift` have been moved unchanged
into `OpenSheafCoproductBaseChange.lean`, in their original namespace. They are
listed in the item's `lean.declarations` and their docstrings now identify this
item. The separate `AlgebraicSpaceRepresentabilityLift.lean` module is removed.
There are no dependency modules or new nodes in the repaired delivery.

These helpers express the original scheme-test cartesian-square definition with
canonical `uliftYoneda.{v}` in place of `yoneda`, allowing section sets in
`Type (max u v)` while tests stay in `Scheme.{u}`. At the original section
universe, `uliftYonedaIsoYoneda` identifies the two conditions. This construction
adds no atlas, covering, arbitrary comparison or equality of universes.

## Second reading by Q81

Repair self-check by the same worker; no independent worker was started, as the
repair prompt forbids other agents. The maintainer's independent review of
`62f959c2e2e8` explicitly accepted the item's statement and proof docstring against
Stacks 02WR. I compared the repaired node and module with that saved packet:
the theorem signature, helper structure, comparison equations, and seven-step
proof docstring are unchanged. The hypotheses still give monic inclusions, open
representability, the sheaf cofan and its induced q, and exactly the site-size
assumption. The conclusions still assert representable sheaves, representability
of q, the unique comparison with both equations, and unique test-change maps with
the cartesian and compatibility conditions. Empty index, empty/repeated summands,
noncovering opens, infinite index and arbitrary test change retain the cases
already checked above. The only found mismatch was the dependency-record
replacement; it has been removed by restoring the complete live record and moving
the two defining expressions into the item module. No statement correction is
needed.

Repair validation on 2026-10-22: the prescribed `scompile.py` compiled the single
repaired file both as a sandbox module (5.6 s) and under its library module name
(7.9 s), with no errors or unexpected warnings. The primary theorem's recorded
signature equals the file verbatim; all lines are at most 100 characters. The
restored dependency node was checked byte-identical to the live copy, with all
21 original names. Its unchanged file introduces no dependency-record diff.
