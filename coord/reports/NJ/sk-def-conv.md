## Worker report

`sk-def-conv` is a convention bundle, not a new Lean notion.  The six clauses in the
node are all supplied by the named statement dependencies: proper, finite, immersion,
surjective, etale, and affine scheme.  Following the established multi-declaration attachment format, I wrote no module and
recorded the existing Mathlib declarations jointly in the node's `lean` record.  The
primary declaration is `AlgebraicGeometry.IsProper`; its `declarations` list records
the interfaces exported by its defining module, and the note identifies the remaining
clauses through their existing statement-dependency records. This is an attachment to
existing conventions, not a claim that `IsProper` alone expresses the whole paragraph.  No proof is required
(the node has `proof: []`).

For the clauses of the statement, the Lean rendering is as follows.

* The ambient objects `X`, `Y`, and the morphism `f : X ⟶ Y` are the Mathlib
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` supplied by
  `def-pc-scheme`.
* “Proper” is the `AlgebraicGeometry.IsProper f` convention from
  `def-weil-proper-morphism`: separated, universally closed, and locally of finite
  type.  The node also cites
  `lem-weil-pbc-universally-closed-quasi-compact`, whose Mathlib match is
  `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed`, so this is equivalent to
  the finite-type formulation in `def-weil-proper-morphism` without adding a
  hypothesis.
* “Finite” is `AlgebraicGeometry.IsFinite f` (and its affine-local finite-algebra
  interpretation), with the integral-algebra companion `IsIntegralHom f`, from
  `def-weil-finite-integral-morphism`; the affine requirement is
  `AlgebraicGeometry.IsAffineHom f` from `pqf-def-affine-morphism`.
* “Immersion” is the factorization supplied by
  `AlgebraicGeometry.IsImmersion`, with closed and open factors respectively
  `AlgebraicGeometry.IsClosedImmersion` and
  `AlgebraicGeometry.IsOpenImmersion`, from `def-weil-closed-immersion` and
  `def-weil-open-immersion`.
* “Surjective” is `AlgebraicGeometry.Surjective f`, i.e. surjectivity of the
  underlying topological map, from `def-weil-surjective-morphism`.
* “Etale” is the `AlgebraicGeometry.Etale f` convention from
  `def-weil-etale-morphism`; its three stated components are
  `AlgebraicGeometry.LocallyOfFinitePresentation f`, `AlgebraicGeometry.Flat f`,
  and the unramified conjunction
  `AlgebraicGeometry.LocallyOfFiniteType f ∧
  AlgebraicGeometry.IsOpenImmersion (CategoryTheory.Limits.pullback.diagonal f)`
  supplied by `def-sbc-locally-finite-presentation`, `def-weil-flat-morphism`, and
  `def-weil-unramified-morphism`.
* “Affine scheme” is the isomorphism-to-spectrum convention from `def-pc-scheme`,
  with `AlgebraicGeometry.Spec (CommRingCat.of A)` from
  `def-weil-affine-spectrum`; the Mathlib affine-scheme predicate is
  `AlgebraicGeometry.IsAffine`.

The statement dependencies used, with their recorded declarations or matches, are:

* `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
* `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`.
* `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, `IsSeparated`, and `UniversallyClosed`.
* `lem-weil-pbc-universally-closed-quasi-compact`: Mathlib instance
  `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed`.
* `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom`.
* `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` and
  `AlgebraicGeometry.IsIntegralHom`.
* `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` and the
  Mathlib immersion factorization theorem `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`.
* `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`.
* `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`.
* `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`.
* `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`.
* `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`.
* `def-weil-unramified-morphism`: the conjunction of
  `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.IsOpenImmersion (pullback.diagonal f)`.
* `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.

I checked edge cases against these component definitions: identity morphisms satisfy
all morphism clauses; `Spec 0` and the empty scheme are permitted affine schemes; an
empty scheme mapping to a nonempty scheme fails only surjectivity; `Spec k[t] → Spec k`
is affine but not finite; and an infinite disjoint union of copies of `Spec k` can be
etale without being quasi-compact.  No extra Noetherian, separated, quasi-compact, or
nonzero-ring hypothesis is introduced.

Searches made for a bundled declaration were:

* `msearch.py ... leanfinder 'bundled conventions for proper finite immersion surjective etale morphisms and affine schemes'`: returned only component-level Mathlib hits (`Scheme.Etale`, `IsFinite.iff_isProper_and_isAffineHom`, affine-target properties), with no bundled convention declaration.
* `msearch.py ... loogle 'AlgebraicGeometry.IsProper, AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsImmersion, AlgebraicGeometry.Etale, AlgebraicGeometry.IsAffine'`: zero hits for a bundled declaration.
* `msearch.py ... grep 'class (IsProper|IsFinite|IsImmersion|Surjective|Etale|IsAffine)' AlgebraicGeometry`: returned the separate Mathlib component classes in `Proper.lean`, `Finite.lean`, `Immersion.lean`, `Etale.lean`, `UnderlyingMap.lean`, `Affine.lean`, and `AffineScheme.lean`.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` for `sk-def-conv`, bundled convention names, and the six component phrases: no project declaration states this six-clause bundle.  The broader project convention nodes are collections of references and do not have this exact six-clause scope.

No new nodes or dependency modules were needed.  No statement correction was needed,
and there is no `STATEMENT-DISPUTED` flag.


Repair/recheck of the preserved attempt: the synchronized node has a stage-1
`reviewed` record by NB, but has no `lean` or `reviewed_lean` record. Thus that review
is not a stage-2 landing and is no reason to stop this assignment. The sandbox's
non-`lean` fields agree with the synchronized node. No repair handoff file
`coord/repair-notes/sk-def-conv.json` is present. I corrected the old report's claim
that the primary `declarations` list contains all six convention predicates.
The scratch check caught an incorrect shortened theorem name; reading the enclosing
namespace confirms `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`.

The full defining modules (all in Mathlib) are `AlgebraicGeometry.Scheme` for
`Scheme`, `Scheme.Hom`, `Spec`, and `Spec.map`; `AlgebraicGeometry.AffineScheme` for
`IsAffine`; `AlgebraicGeometry.OpenImmersion` for `IsOpenImmersion`; and
`AlgebraicGeometry.Morphisms.<Name>` with `<Name>` respectively `Proper`,
`Separated`, `UniversallyClosed`, `FiniteType`, `QuasiCompact`, `Affine`, `Finite`,
`Integral`, `ClosedImmersion`, `Immersion`, `UnderlyingMap`, `Etale`,
`FinitePresentation`, and `Flat` for the corresponding predicates. The immersion
factorization theorem is `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists` in `Immersion`.
The proper bridge is `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed` in
`UniversallyClosed`. Affineness uses `Scheme.isoSpec`, and étaleness uses
`Etale.iff_flat_and_formallyUnramified` together with the two diagonal instances
in `FormallyUnramified`. These defining signatures and docstrings were read in the
pinned sources; each is used through the already-recorded dependency, with no
private copies.

Repeated searches in this repair: `msearch.py NJ sk-def-conv leanfinder` with
“proper finite immersion surjective etale morphisms and affine schemes definitions”
returned eight component or general-framework hits (`IsAffineHom`, `IsFinite`,
`IsPreimmersion`, `IsFinite.iff_isProper_and_isAffineHom`, etc.), with no bundled
notion. `loogle` with `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsFinite,
AlgebraicGeometry.IsImmersion, AlgebraicGeometry.Etale` returned zero hits. `grep`
with `class (IsProper|IsFinite|IsImmersion|Surjective|Etale|IsAffine)` in
`AlgebraicGeometry` returned the eight separate component classes (one unrelated
`SurjectiveOnStalks`). Exact-id `rg` across upstream `WeilConjectures` and the
side library `lean/Sheaf` returned no hits. A broad component-name search found
uses in upstream `ChowLemma`, `EtaleFiniteRefinement`, `Curve`, and similar modules,
not another six-clause definition. The source paragraph at
`main-20261015/blueprint/sec-nagata-compactification/sk-def-conv/_section.md`
agrees with these conventions. Remote search hits named `IsEtale` were checked
against the pinned source: the current class is `Etale`, and `IsEtale` is a
deprecated alias; the attachment uses the class.

Validation: `scompile.py NJ sk-def-conv scratch/ExistingConventionsCheck.lean`
completed with exit 0 and no warnings. Its scratch import-and-`#check` file checks
every component predicate and the proper, immersion, étale and affine interfaces
in both the sandbox and library checks (3.5 s and 2.9 s).
The scratch file is not a delivered module. The required `deliver2.py --no-push`
then compiles its own existing-declaration probe and runs server preflight.
No mathematical statement or dependency list changed; no new node is necessary.

## Second reading by NJ

I independently read the current node, the sandbox's complete `lean` record,
the exact blueprint paragraph at
`main-20261015/blueprint/sec-nagata-compactification/sk-def-conv/_section.md`,
and every direct statement-dependency node. The source paragraph assumes only
schemes and a scheme morphism; it has no ambient field, Noetherian, finiteness,
or nonemptiness hypothesis. It is a list of six conventions, not a predicate
asserting that one morphism has all five morphism properties simultaneously.
The following is my object/hypothesis/clause inventory and its Lean match.

1. Objects: arbitrary schemes `X Y : AlgebraicGeometry.Scheme.{u}` and
   `f : X ⟶ Y`. I read `Scheme.local_affine`, `Scheme.Hom`, `Spec`, and
   `Spec.map` in `Mathlib.AlgebraicGeometry.Scheme`. These are schemes and
   morphisms of locally ringed spaces, as supplied by `def-pc-scheme` and
   `def-weil-affine-spectrum`, with no additional structure on `f`. Verdict: pass.
2. Proper: the three conditions are `IsSeparated f`, `LocallyOfFiniteType f`,
   and `UniversallyClosed f`. The recorded primary declaration is literally
   `class IsProper : Prop extends IsSeparated f, UniversallyClosed f,
   LocallyOfFiniteType f where`, under `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
   I read the separated closed-diagonal field and universal closedness field,
   rather than substituting a topologically proper map. The bridge to the
   dependency's finite-type wording is the existing
   `instQuasiCompactOfUniversallyClosed`, recorded by
   `lem-weil-pbc-universally-closed-quasi-compact`. Stacks 01W1 and 04XU
   confirm this equivalence without any extra hypothesis. Verdict: pass.
3. Finite: `IsFinite f` extends `IsAffineHom f` and has
   `finite_app (f) (U : Y.Opens) (hU : IsAffineOpen U) :
   (f.app U).hom.Finite`. I read both classes and the finite/integral
   dependency record. This is the finite-module condition on every inverse
   image of an affine open, exactly Stacks 01WH(2). The dependency explicitly
   interprets the source's finite pushforward algebra as a finite type
   quasi-coherent module; Stacks 01PB gives the affine module/sheaf equivalence.
   This is not just finite type as an algebra. `IsIntegralHom` is an existing
   companion interface, not an additional condition in this clause. Verdict: pass.
4. Immersion: `IsImmersion f`, through the existing
   `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`, means
   `∃ (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
   IsClosedImmersion g₁ ∧ IsOpenImmersion g₂ ∧ g₁ ≫ g₂ = f`.
   I read this exact theorem, its surrounding namespace, and the two immersion
   definitions. Thus the closed factor comes first and the open factor second,
   with no quasi-compactness restriction and no reversed-factor replacement.
   Stacks 01IO(5) uses the same factorization. Verdict: pass.
5. Surjective: `AlgebraicGeometry.Surjective f` has exactly the field
   `surj : Function.Surjective f`. This is surjectivity on underlying spaces,
   not an epimorphism or surjectivity on stalks; Stacks 01RZ agrees. Verdict: pass.
6. Etale: `AlgebraicGeometry.Etale f` is affine-locally the ring-map etale
   condition. I read the full class and `Etale.iff_flat_and_formallyUnramified`,
   whose conclusion is `Etale f ↔ Flat f ∧ FormallyUnramified f ∧
   LocallyOfFinitePresentation f`. I also read the locally-finite-presentation
   and flat signatures, the instance from an open diagonal to formal
   unramifiedness, and `FormallyUnramified.isOpenImmersion_diagonal`, which
   assumes locally finite type in the other direction. Locally finite
   presentation supplies that latter condition. Therefore the recorded etale
   dependency is exactly locally finite presentation, flatness, and the
   unramified dependency's `LocallyOfFiniteType f ∧
   IsOpenImmersion (pullback.diagonal f)`. Stacks 02GE and 02GV confirm both
   directions. The current class is `Etale`; the search index's `IsEtale` is
   a deprecated alias and is not used. Verdict: pass.
7. Affine scheme: `AlgebraicGeometry.IsAffine X` says that the canonical
   `X.toSpecΓ` is an isomorphism, and `Scheme.isoSpec X` gives
   `X ≅ Spec Γ(X, ⊤)`. Spectra are affine, and affineness transports across
   isomorphisms, giving exactly existence of an isomorphism with `Spec A`
   for a commutative ring. I read `IsAffine`, `Scheme.isoSpec`, and the
   spectrum dependency, and Stacks 01HW. Verdict: pass.

The recorded dependency modules were opened at the declaration signatures:
`Scheme`; `Morphisms.FiniteType`; `Morphisms.Proper` (with `Separated` and
`UniversallyClosed`); `Morphisms.QuasiCompact`; `Morphisms.Affine`;
`Morphisms.Finite` and `Integral`; `Morphisms.ClosedImmersion` and `Immersion`;
`OpenImmersion`; `Morphisms.UnderlyingMap`; `Morphisms.Etale` and
`FormallyUnramified`; `Morphisms.FinitePresentation`; and `Morphisms.Flat`.
`AffineScheme` supplies the affine-scheme predicate. All are Mathlib modules.
The universally-closed node and the affine/finite-presentation nodes with only
Mathlib matches are usable as recorded; no missing dependency interface was found.

Edge cases: identity morphisms and empty schemes are admitted. The zero ring is
a commutative ring and its spectrum is the empty affine scheme. The empty scheme
mapping to a nonempty scheme satisfies the local/finite/immersion conditions but
fails surjectivity, as the source requires. `Spec k[t] → Spec k` separates affine
from finite. An infinite disjoint union of copies of `Spec k` is etale without
being quasi-compact, so no global finite-presentation condition was inserted.
There is no numerical parameter or characteristic restriction. The arbitrary
scheme universe `u` is retained; schemes in different initial size universes
can be placed in a common larger universe. There is no smaller independent
test-scheme universe that could make universal closedness vacuous. Verdict: pass.

Independent searches on this reading:

- LeanFinder, `scheme map proper separated universally closed finite affine
  immersion open closed etale convention`: eight component hits, including
  `IsProper`, `UniversallyClosed`, `IsImmersion`, `IsFinite`, and
  `IsPreimmersion`; no new bundled notion.
- Loogle, `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists`: one exact hit
  with the closed-then-open factorization and no extra hypothesis.
- Indexed grep, `finite_app|isImmersion_iff_exists|iff_flat_and_formallyUnramified`
  in `AlgebraicGeometry`: fifteen hits, including the finite class field,
  the unrestricted immersion equivalence, its distinct quasi-compact variant,
  and the etale equivalence. I read the relevant source declarations locally.
- Direct `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for
  `sk-def-conv`, scheme/morphism convention names, and the component predicates:
  no competing six-clause definition. The upstream immersion module extends
  Mathlib's existing predicate and does not introduce a replacement. The
  upstream-name index records the same component notions. I also opened the
  existing broader DAG convention bundles; they cite these components and do
  not require a new definition here.

The attachment is a collection of existing conventions through its named
dependencies. In particular, `IsProper` alone does not render the whole paragraph;
the note explicitly supplies the other clauses through their authoritative
dependency records. The optional `declarations` list consists of existing
interfaces available from the primary module, and is not a claim to exhaust the
six clauses. I checked the primary signature verbatim against its source line.
No new module, new definition node, dependency module, theorem proof, or hollow
definition is needed. Existing Mathlib source docstrings are not rewritten to
add blueprint tags. The node has no proof steps to postpone, and no statement
correction or citer audit is necessary.

I found no mathematical or binding mismatch requiring a change. I left the node
and the Worker report in place and added this missing independent second reading.
Validation on this reading: `scompile.py NJ sk-def-conv
scratch/ExistingConventionsCheck.lean` passed with exit 0, no errors, and no
warnings in both sandbox and library positions (3.1 s and 2.9 s). The probe
checks every component and the equivalence interfaces above; it remains scratch
work and is not part of the delivered Lean library. The required delivery dry
run also compiles the primary module's recorded existing interfaces and runs
the server preflight.
