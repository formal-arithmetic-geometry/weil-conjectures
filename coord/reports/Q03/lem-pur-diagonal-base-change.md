## Worker report

Item: lem-pur-diagonal-base-change. Worker: Q03 stage 2, 2026-10-16.

The module `lean/Sheaf/Paper/PurityDiagonalBaseChange.lean` states
`WeilConjectures.PurityFiniteSetting.diagonalBaseChange`. No mathematical proof is
attempted: its proof is `sorry`. All helper definitions have actual data.
The source is the node's blueprint, sec-smooth-purity/sk-thm-smooth-purity,
lem-pur-diagonal-base-change, order 2009. The mathematical statement is unchanged.

Hypothesis and clause correspondence:

- The purity conventions are the recorded `WeilConjectures.PurityFiniteSetting`
  from `Sheaf.Paper.PurityFiniteSetting`. This includes the finite field, its
  algebraic closure, the distinct prime, finite coefficient extension and positive
  quotient level. `P.Coefficient` is the actual quotient with its standard size lift.
  As def-pur-conventions expressly stipulates, the construction is at Lambda=A;
  integral, rational and algebraically closed versions are coefficient transports.
- `X Y : Scheme.{u}` and the structure maps `aX`, `aY`, with
  `LocallyOfFiniteType` and `QuasiCompact`, say they are finite-type k-schemes.
  `hf : f ≫ aY = aX` says f is a k-morphism. Both schemes and all test schemes
  use the same scheme universe; the module coefficient category has Hom universe
  u+1, as in the published pro-etale framework.
- `[IsSeparated f]` is precisely relative separatedness, and
  `[SmoothOfRelativeDimension d f]`, `d : Nat`, is smoothness of pure relative
  dimension d. There is no properness or absolute-separatedness hypothesis.
- W is `pullback f f`, with p1=`pullback.fst f f`, p2=`pullback.snd f f`,
  Delta=`pullback.diagonal f`. These are Mathlib's actual fibre product and maps.
- The first conjunct of `DiagonalBaseChangeConclusion` is
  `IsPullback p2 p1 f f`, exactly the square with upper p2 and left p1.
  Its second conjunct is `Smooth p1`.
- b1 is `Lp2* omega_f ≅ omega_p1`, and b2 is `Lp1* omega_f ≅ omega_p2`.
  Their inverses give the two displayed isomorphisms in the node's direction.
  The following two conjuncts require `IsDualizingBaseChangeIso` for the
  corresponding canonical Cartesian squares. Thus these are the specified
  counit mates, not arbitrary isomorphisms between the indicated objects.
- The final isomorphism e has source `sectionInvariant p1 aX Delta` and target
  `dualizing f aY`. The equality `e = diagonalRestrictionIso ... b1`
  specifies its actual chain: pull back b1 inverse, apply inverse pullback
  composition, apply the equality Delta≫p2=id, and apply identity pullback.
  `sectionInvariant` is definitionally LDelta* omega_p1, so both intermediate
  objects and both arrows of the displayed chain are retained.
- `DiagonalBaseChangeConclusion` supplies Noetherian and compactification
  instances inside its definition, from finite type over the field and relative
  separatedness. These are consequences, not extra theorem hypotheses. There
  are no let/have binders in the theorem signature.

The canonical base-change equation is written without choosing an inverse to a
postponed exchange theorem. For every etale-origin witness, exchange followed
by Rf'! of b and its counit equals the pulled-back original counit followed by
the unit comparison. `plusEtaleOrigin` is included to ensure this is not a
vacuous quantification. On these finite constructible inputs the exchange is
invertible, so this is exactly the adjoint-transpose equation of
`def-pur-co-smoothness`. `compactSupportOriginIso` uses the published
compactification-independence map to compare the base-changed compactification
with the chosen one. It conjugates by the witness; it chooses no arbitrary map.

For clause 2 of the dependency definition, the Lean existential is the canonical
mate phi with source omega_f tensor Lf*K, in the order used by the published
projection map. Its counit equation is PF followed by Rf!phi and epsilon equals
epsilon_at_unit tensor id, followed by the left unitor. The source's theta is
canonical symmetry followed by phi. Symmetry is always an isomorphism, so
"phi is an isomorphism" is exactly "theta is an isomorphism". This equivalent
factor order leaves both canonical mate conditions intact and avoids repeatedly
normalizing the signed derived braiding in the specialized predicate.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and
  its coefficient and field projections (recorded def-pur-conventions).
- Mathlib: `AlgebraicGeometry.SmoothOfRelativeDimension`, `Smooth`,
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `CategoryTheory.Limits.pullback`,
  its projections, diagonal and diagonal identities, and `IsPullback`.
- The supplied `Sheaf.Paper.FiniteTypeExceptionalInverseImage`:
  `PurityFiniteSetting.exceptional`, `dualizing`, `counit`, and their named
  finite-coefficient/Noetherian/bounded-below/unit proof interfaces.
- The supplied `Sheaf.Paper.PuritySectionInvariant`:
  `PurityFiniteSetting.sectionInvariant` and `sectionInvariant_invertible`.
- The supplied `Sheaf.Paper.CohomologicalSmoothness`:
  `AlgebraicGeometry.ProEtale.IsCohomologicallySmooth`, `IsDualizingBaseChangeIso`,
  `compactSupportOriginIso`, and the specified tensor mate helpers from Q11.
- Published `WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar`:
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp`,
  `leftDerivedUpperStarCongr`, `leftDerivedUpperStarId`, and
  `ProEtale.upperStar ... |>.leftDerivedFunctor`.
- Published pro-etale `Derived.Duality`, `Derived.LowerShriekIndependence`,
  `Derived.LowerShriekBaseChange`, `Derived.LowerShriekProjection`,
  `Derived.UpperStarMonoidal.Comparison`, and `Derived.TorAmplitude`:
  the transported exceptional functor and counit, compactification-independence
  comparison, exchange, projection map, unit pullback comparison, and the
  bounded-constructible finite-Tor predicate.

Edge cases checked: d=0 (no positive-dimension assumption), empty X or Y
(fibre product, diagonal and all derived operations remain defined), n=1
(the actual positive finite quotient), and schemes that are not absolutely
separated (only f's separatedness is used). The diagonal is a closed section
because f is separated. No orientation or identification with a Tate twist is
inserted. No ambient pro-etale right adjoint is postulated. A base map in the
cohomological-smoothness predicate is arbitrary, including the identity and f
itself; the canonical maps include their unit normalizations.

Searches:

- msearch.py LeanFinder, `base change dualizing complex pullback fst diagonal
  section invariant`: eight unrelated Mathlib pullback/tensor-product results;
  no exact result.
- msearch.py Loogle,
  `nonempty_iso_dualizingComplex_pullbackFst, nonempty_iso_sectionInvariant_diagonal`:
  no indexed match (upstream names are not Mathlib declarations).
- msearch.py grep, `dualizingComplex|sectionInvariant|upperShriek`,
  Mathlib/AlgebraicGeometry: no matches.
- msearch.py LeanSearch, `dualizing complex self fibre product base change
  diagonal section invariant`: service unavailable, Internal Server Error;
  no verdict inferred from unavailability.
- rg on slopmaster2 WeilConjectures and the shared Sheaf library, and the
  blueprint-id search: upstream EtaleCohomology/Purity/Smooth/Basic has the
  Nonempty etale isomorphisms `nonempty_iso_dualizingComplex_pullbackFst`,
  `...pullbackSnd`, `...sectionInvariant_diagonal`. They are not the specified
  pro-etale counit mates and cannot serve as this statement's record.
- Read the exact shared published pro-etale framework, including the full
  signatures/docstrings of the operations used. Read current server sources
  with scompile.py --source and checked delivery branches for unstated
  prerequisites; no usable complete recorded prerequisite was found.

No STATEMENT-DISPUTED issue or source correction is asserted.

## Dependency modules

Previously unstated def-weil-exceptional-inverse-image, def-pur-section-invariant
and def-pur-co-smoothness are supplied in the three modules listed above, with
lean-only node records. Their finite-level interfaces use the actual published
operations, as required by the finite purity conventions. The exceptional
functor is the etale exceptional right adjoint transported by nu_X* and Rnu_Y*;
its bounded-below instance is a named theorem, not an extra geometric hypothesis
or an ambient pro-etale adjoint. The section invariant is actual derived
pullback, with the stated invertibility theorem. The cohomological-smoothness
predicate includes all three clauses, with tensor and base-change mates
specified by their counit equations.

The older recorded inverse-image and ringed pullback-composition modules import
an obsolete FiniteCoefficient pro-etale framework whose declarations collide
with the current published framework. Following the launcher's duplicate-import
repair instruction, the diagonal module imports the published
Derived.UpperLowerStar module and uses its actual finite-coefficient pullback,
composition and identity maps. It does not import both frameworks or redefine
a pullback. The originally recorded general ringed interfaces are not edited.

The previously unstated def-weil-derived-pullback-tensor-hom receives an
`existing: true` record for the published ProEtale.derivedHom, derivedTensor,
and exact upperStar (derived via leftDerivedFunctor), at the finite stage used
here. No copy of an operation is introduced.

The def-weil-finite-tor-amplitude record is repaired to the equivalent published ModuleCat-valued
finite interface: its original SheafOfModules predicate cannot directly accept
the published exceptional functor's objects. Moreover the old module imports
ProEtaleInverseImage through ProEtaleBoundedConstructibleTriangulated and hence
the obsolete FiniteCoefficient framework, so it cannot coexist with the current
framework. The record's note preserves the locations of the already-defined
integral and field interfaces. Both finite encodings use bounded constructibility
and finite Tor amplitude; neither condition is omitted.

## Validation

Every delivered Lean module is checked separately through scompile.py; no lake
build or direct compiler invocation is used. The final `deliver2.py Q03 lem-pur-diagonal-base-change --no-push` printed
`OK (dry run)` for commit `0c2c612323`: every file compiles and preflight passes
except for the independent second reading, which the second reader supplies.
The complete output is in `scratchpad/dry-run-repaired.log`. Nothing was pushed.


## Resumption audit

Re-read the original blueprint item and its unit on the server (the literature
copy is absent on this worker machine). The source confirms both projection
comparisons and the diagonal restriction chain; no statement correction is needed.
Re-ran LeanFinder (canonical smooth dualizing base change on a self product),
Loogle (`CategoryTheory.Functor.mapIso`) and Mathlib grep
(`dualizingComplex|sectionInvariant|upperShriek`, AlgebraicGeometry).
The eight semantic hits were scheme-module pullbacks or Kaehler differential
base-change lemmas; Loogle returned functorial-isomorphism identities; grep
returned no matches. None states the requested assertion.

The prior specialized tensor-mate structure timed out in kernel checking.
A categorical factoring experiment also exceeded the limit. A delivery-branch
check found Q11's already compiled common interfaces. This delivery now reuses
its module paths and declarations: `AlgebraicGeometry.ProEtale.IsCohomologicallySmooth`
and `finiteTypeExceptionalInverseImage`, including the generic coefficient-category
helper for the derived left unitor. The former specializes the same counit
conditions after constructing the mapwise finite-type exceptional interface.
The module is extended only by `compactSupportOriginIso` and
`IsDualizingBaseChangeIso`, the specific canonical comparison predicates the
current item needs. The exceptional owning module also retains the finite-setting
specializations used in this item. There is one owning module per dependency and
no second cohomological-smoothness definition.

Q11's delivered definition expresses its three clauses as the named
`cohomologicalInvertibilityClause`, `cohomologicalTensorClause` and
`cohomologicalBaseChangeClause`. It builds the finite coefficient instance from
`Padic.finite_coefficientExtensionRing`, and it supplies the bounded-below
right-adjoint interface mapwise via `finiteTypeHasBoundedBelowUpperShriek`.
N6's exceptional branch and NR's smoothness-theorem branch have no Lean record;
there is no additional usable statement there.

Postponed statements, all named and recorded in their owning node:
`finiteCoefficient`, `exceptionalBoundedBelow`, `noetherian`, `unitPlus`,
`finiteTypeHasBoundedBelowUpperShriek` (def-weil-exceptional-inverse-image),
`sectionInvariant_invertible` (def-pur-section-invariant), and
`diagonalBaseChange` (the item). Each carries its source and natural-language
proof. No definition has postponed data.

## Second reading by Q03

I independently opened the node `lem-pur-diagonal-base-change`, its blueprint
source entry, and `PurityDiagonalBaseChange.lean`. The item-by-item reading is:

* The fixed purity setting is `P : PurityFiniteSetting`; its field, coefficient,
  and positive quotient level are supplied by `P` and `P.Coefficient`.
* The schemes and structure maps are `X Y : Scheme.{u}`, `aX` and `aY`, with
  `LocallyOfFiniteType` and `QuasiCompact` hypotheses. The equation
  `hf : f ≫ aY = aX` renders that `f` is a morphism over the fixed field.
* `d : ℕ`, `[IsSeparated f]`, and `[SmoothOfRelativeDimension d f]` render
  smooth separated pure relative dimension `d`; no properness or absolute
  separatedness is added.
* `pullback f f`, `pullback.fst f f`, `pullback.snd f f`, and
  `pullback.diagonal f` render `W`, `p₁`, `p₂`, and `Δ` respectively.
* `IsPullback (pullback.snd f f) (pullback.fst f f) f f` is the displayed
  Cartesian square, and `Smooth (pullback.fst f f)` is its smooth projection
  clause.
* The existential `b₁` has endpoints `Lp₂* ω_f` and `ω_{p₁}`; `b₂` has
  endpoints `Lp₁* ω_f` and `ω_{p₂}`. Their endpoint order is the canonical
  base-change direction, while the node's displayed inverse is represented by
  the inverse isomorphism. `IsDualizingBaseChangeIso` records the specified
  counit-mate equations from `def-pur-co-smoothness`, so these are canonical
  comparisons rather than arbitrary endpoint isomorphisms.
* The existential `e` has endpoints `sectionInvariant p₁ aX Δ` and
  `dualizing f aY`; `e = diagonalRestrictionIso f aX aY b₁` renders exactly the
  node's pullback of `b₁⁻¹`, pullback-composition comparison, `p₂ Δ = id`, and
  identity-pullback comparison.

The local instance bindings inside `DiagonalBaseChangeConclusion` supply the
Noetherian, compactification, quasi-compact, and smooth consequences of the
finite-type field hypotheses. They do not introduce proposition hypotheses or
change the theorem signature. The theorem itself has only the node's data and
hypotheses, and its proof remains `sorry`.

I checked the edge cases covered by the source: `d = 0`; empty `X`, `Y`, or
the fibre product; positive quotient level `n = 1`; arbitrary characteristic
of the fixed finite field subject to the purity conventions; and schemes that
are not absolutely separated. No index set or nonzero-object assumption is
introduced, and no Tate twist, orientation, or ambient pro-etale right adjoint
is added.

I repeated the Mathlib, slopmaster2, and shared-`lean/Sheaf` searches recorded
by the worker (LeanFinder/LeanSearch/Loogle and grep for
`dualizingComplex`, `sectionInvariant`, `upperShriek`, and the full semantic
phrases). The matches are ordinary scheme pullback or module-pullback facts;
none states this dualizing base-change assertion. The three supplied
dependency modules were read against their node records: the exceptional
inverse image is the finite-type field construction, section invariant is
derived pullback along the section, and cohomological smoothness has the three
specified canonical clauses. The repaired published finite-Tor and derived
pullback interfaces are the ones imported by the module; no private duplicate
notion is present.

No mismatch was found, so no Lean or node statement was changed in this second
reading. All four sibling modules compile separately through `scompile.py`;
the only diagnostics are the permitted postponed-proof (`sorry`) warnings.
