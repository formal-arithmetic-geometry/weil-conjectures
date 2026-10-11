## Worker report

The module `Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicityOfBaseChange` states
`AlgebraicGeometry.Etale.hasAllPrimeInjectiveAcyclicity_of_hasTorsionAbelianBaseChange`.
Its proof is `sorry`; no definition contains `sorry`, and nothing is proved in this delivery.
The item statement, dependencies and proof are unchanged. Two dependency records require
specializations, described below; only their `lean` fields change.

Hypothesis and clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u_forward}}`, with every universe explicitly declared.
- The morphism f: `(f : X ⟶ Y)`.
- Properness: `[IsProper f]`, Mathlib's separated, universally closed, locally finite type
  predicate; universal closedness implies quasi-compactness and hence finite type.
- PBC for torsion abelian sheaves: `(hf : HasTorsionAbelianBaseChange f)`. Its definition
  quantifies over every base-change morphism and every cartesian square using
  `(sq : IsPullback g' f' f g)`, every `F : Sheaf X.smallEtaleTopology AddCommGrpCat`,
  and `F.IsTorsion`. It requires `IsIso` of the specified
  `derivedBaseChangeMapPlus AddCommGrpCat sq.toCommSq` at `singleFunctor ... 0` applied
  to F, precisely F placed in degree zero. It imposes no hypothesis on the base change.
- Conclusion for every prime r: `HasAllPrimeInjectiveAcyclicity f` unfolds to
  `∀ r : ℕ, r.Prime → HasPrimeInjectiveAcyclicity f r`.
- In each IA_r, arbitrary cartesian base change is the same `IsPullback` quantification.
- Every injective F_r-module sheaf I: the binder is a sheaf valued in
  `ModuleCat.{u_ia + 1} (ULift.{u_ia + 1} (ZMod r))`, followed by `Injective I`.
  For prime r this coefficient ring is F_r. ULift only supplies the universe needed
  by the source's six-functor encoding and is canonically ring-isomorphic to ZMod r.
  Injectivity is in this module-sheaf category, not in the abelian-sheaf category.
- The pullback g'^{-1}I: first `sheafCompose` with `forget₂ ModuleCat AddCommGrpCat`
  takes the underlying abelian sheaf, then `upperStar AddCommGrpCat g'` pulls it back.
  This spells out the abelian sheaf whose higher direct images the node requests.
- R^q f'_* of that sheaf: `singleFunctor ... 0`, then
  `(lowerStar AddCommGrpCat f').rightDerivedFunctorPlus`, then
  `DerivedCategory.Plus.homologyFunctor ... q`.
- Vanishing for every q > 0: `∀ q : ℤ, 0 < q → IsZero (...)`.
  Nonnegative integer higher images are represented inside integer-indexed D-plus.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChange` (dependency module in this delivery):
  `AlgebraicGeometry.Etale.HasTorsionAbelianBaseChange`.
- `Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicity` (dependency module in this delivery):
  `AlgebraicGeometry.Etale.HasPrimeInjectiveAcyclicity`,
  `AlgebraicGeometry.Etale.HasAllPrimeInjectiveAcyclicity`.
- `WeilConjectures.SixFunctors.BaseChange.Square`:
  `AlgebraicGeometry.Etale.squareUpperStarIso`, used by the recorded exchange construction;
  `IsPullback` and its `toCommSq` encode the chosen cartesian square.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, specialized to AddCommGrpCat.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` and `rightDerivedLowerStarPlus` (the latter
  is the abbreviation for `lowerStar.rightDerivedFunctorPlus`).
- The mixed record for `def-weil-pbc-etale-sheaves` explicitly records the existing
  `CategoryTheory.Sheaf`, `ModuleCat` encoding, and `CategoryTheory.Sheaf.IsTorsion`;
  those notions are used. Its unrelated set-valued constructibility definitions are
  not needed. `Sheaf.IsTorsion` is read in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` and reused verbatim.

Edge cases checked mathematically: identity f gives the expected positive-degree
vanishing; the zero sheaf and empty schemes give zero objects; q = 0 is deliberately
excluded and no claim that f_*I vanishes is made. All primes including the residue
characteristic and 2 are included; 0 and 1 are excluded by `r.Prime`. The lift of ZMod r
retains every prime-field module of the coefficient universe, and the same scheme
universe is used for every test scheme. No finite-type or separation condition on g
is introduced. Unlike the source's module-valued IA predicate, there is no additional
torsion hypothesis on I: being an F_r-module already implies it.

Searches for reuse (actual searches are logged in `searches.jsonl`):

- `msearch.py leanfinder`: "proper base change for torsion abelian etale sheaves implies
  higher direct image vanishing for injective prime field module sheaves". Eight generic
  results, including `Functor.isZero_rightDerived_obj_injective_succ` and K-injective
  complexes, none the abelian-to-prime-field implication.
- `msearch.py loogle`: "AlgebraicGeometry.Etale.HasTorsionBaseChange,
  AlgebraicGeometry.Etale.HasInjectiveAcyclicity". Unknown identifier; no Mathlib hits.
- `msearch.py grep`: "HasTorsionBaseChange|HasInjectiveAcyclicity|derivedBaseChange".
  No Mathlib hits.
- `msearch.py leansearch`: "proper base change torsion abelian sheaf injective prime
  field acyclicity". Service unavailable (Internal Server Error).
- `rg` on source `WeilConjectures`, project `lean/Sheaf`, and upstream names for all
  four proposed declaration names: none exist. `grep -rn` of the item id in the source
  gives no hit. The existing source module `BaseChangeProperty.lean` was read in full:
  its `HasTorsionBaseChange.hasInjectiveAcyclicity` is module-valued for a fixed ring,
  as the node's old lean note already warns, and is not this statement.
- `rg` for base-change and injective-acyclicity names in the project's Lean found no
  specialization to torsion abelian PBC or all prime-field injectives.

Source checked directly: [Stacks Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B),
Lemma 59.91.6, (1) implies (2). The local Stacks tex file is absent on this machine.
The source lists every prime and every injective Z/lZ-module sheaf, with q > 0;
its forward direction and the DAG's expanded proof agree with this statement.
No statement dispute or correction was necessary.

## Dependency modules

`def-weil-pbc-property`: the recorded `HasTorsionBaseChange Λ f` quantifies over
module-valued derived objects with torsion cohomology, whereas this node explicitly
requires torsion abelian sheaves placed in degree zero. The delivery supplies
`HasTorsionAbelianBaseChange`, retaining the source's specified derived exchange map
at AddCommGrpCat and the existing sheaf torsion predicate. This is exactly the
node's definition, with no duplicate exchange construction or torsion notion.

`def-weil-pbc-injective-acyclicity-property`: the recorded `HasInjectiveAcyclicity Λ f`
quantifies over injective torsion module sheaves over arbitrary Λ. The dependency
node instead specifies IA_r and its quantification over every prime. The delivery
supplies `HasPrimeInjectiveAcyclicity` and `HasAllPrimeInjectiveAcyclicity`, with no
extra torsion hypothesis, keeping higher direct images abelian-valued after explicitly
forgetting coefficients. Both dependency records have a note explaining the old
record's mismatch. All other fields of those nodes remain unchanged.


## Second reading by M1

I read the item and all seven statement dependencies, both delivered dependency
modules, their dependency nodes, and the source declarations themselves. I obtained
Stacks `etale-cohomology.tex` in the sandbox scratchpad and read Section
`section-proper-base-change`, the definition immediately before
`lemma-proper-base-change-in-terms-of-injectives` (Tag 0A4B), its two assertions,
and the proof. The section imposes no standing Noetherian, base-field, or
characteristic hypothesis. The lemma assumes only a proper scheme morphism;
its (1) uses torsion abelian sheaves and its (2) uses injective Z/lZ-module
sheaves and every cartesian base change. The node expands the source's forward
implication without changing its statement. There is no statement correction.

Object, hypothesis, and conclusion checklist (verdicts refer to the repaired delivery):

- X and Y are schemes: `{X Y : Scheme.{u_forward}}`. PASS, arbitrary schemes,
  not schemes over a field or Noetherian schemes.
- f is a scheme morphism: `(f : X ⟶ Y)`. PASS.
- f is proper: `[IsProper f]`. PASS. I opened Mathlib's `IsProper`;
  separated + universally closed + locally finite type is finite type because
  universally closed supplies quasi-compactness. No additional instance is bound.
- PBC(f) holds for torsion abelian sheaves: `hf : HasTorsionAbelianBaseChange f`.
  PASS after repair. Its F binder is `Sheaf X.smallEtaleTopology AddCommGrpCat`;
  its torsion hypothesis is now `Scheme.IsTorsionAbelianSheaf F`, precisely the
  recorded declaration of `def-weil-pbc-torsion-etale-sheaf`. I opened its body:
  it requires `IsIso (colimit.desc D c)` for the positive-integer divisibility
  diagram of kernels of multiplication, rather than torsion of all section groups.
- Every base change g:Y'→Y and associated square: both dependency definitions
  quantify over `Y' X' : Scheme` and `g`, `f'`, `g'`, then
  `IsPullback g' f' f g`. PASS. There is no condition on g. I opened `IsPullback`:
  its commuting equality and limiting cone yield the uniquely compatible
  identification with the fibre product, hence no chosen identification is lost.
- PBC concerns the specified exchange map on F[0]:
  `IsIso ((derivedBaseChangeMapPlus AddCommGrpCat sq.toCommSq).app
  ((DerivedCategory.Plus.singleFunctor _ 0).obj F))`. PASS.
  I opened `squareUpperStarIso` and `derivedBaseChangeMapPlus`; these are the
  recorded square comparison and derived exchange transformation, not an
  existential isomorphism of objects. The latter has source Rf_* followed by
  derived g^{-1} and target derived g'^{-1} followed by Rf'_*.
- Conclusion for every prime r: `HasAllPrimeInjectiveAcyclicity f` means
  `∀ r : ℕ, r.Prime → HasPrimeInjectiveAcyclicity f r`. PASS.
- Every injective F_r-module sheaf I on X_et: the binder in IA_r is
  `Sheaf X.smallEtaleTopology (ModuleCat (ULift (ZMod r)))`, with `Injective I`.
  PASS. Injectivity is in module sheaves, not the category of underlying
  abelian sheaves. ZMod r is Z/rZ; the ULift ring has the same elements and
  operations up to its canonical ring equivalence. No finite-generation or
  extra torsion condition on I is imposed. The six-functor module-sheaf encoding
  is the accepted encoding recorded in `def-weil-pbc-etale-sheaves`.
- Pullback g'^{-1}I: `sheafCompose` with `forget₂ ModuleCat AddCommGrpCat`, then
  `upperStar AddCommGrpCat g'`. PASS. I opened `upperStar`: sheafified left Kan
  extension, left adjoint to the small-etale direct image. Forgetting constant
  coefficients before this gives the underlying abelian inverse image requested.
- Higher direct images: `(lowerStar AddCommGrpCat f').rightDerivedFunctorPlus`
  on the pullback in degree zero, then `DerivedCategory.Plus.homologyFunctor _ q`.
  PASS. I opened `lowerStar`: evaluation at the fibre product, as the direct-image
  node says. This is the recorded Rf'_*, not a different cohomology functor.
- Vanishing for every q>0: `∀ q : ℤ, 0 < q → IsZero (...)`. PASS. IsZero is in
  abelian sheaves, and positive integers are precisely positive natural degrees.
  Universally quantified square and I may exchange order with r, since their
  quantifiers are universal; the Lean preserves the required dependencies.

The dependency modules correctly replace the unusable source records: source
`HasTorsionBaseChange Λ f` requires all module-valued derived objects with torsion
cohomology, whereas this PBC node requires abelian sheaves in degree zero.
Source `HasInjectiveAcyclicity Λ f` requires torsion module injectives at a fixed
ring and module-valued vanishing; this IA node requires all prime fields and
abelian-valued vanishing. I read `BaseChangeProperty.lean` definitions and its
forward theorem, which does not give this exact signature. The delivered
predicates are defined on arbitrary f but used under the theorem's properness
binder; on every proper f their bodies are exactly the node's properties.
No new definition nodes or private exchange/derived-image constructions are added.

Edge cases: zero I and zero F remain admitted; empty X, Y, X', Y' are not
excluded by any binder. The empty covering case is handled by the site's sheaf
condition and colimit definition. There is no index-set nonemptiness hypothesis.
q=0 is deliberately excluded; q<0 is not asserted. All primes, including 2 and
the scheme's characteristic, are included; 0 and 1 are excluded only by Prime.
All schemes are in one arbitrary universe, including all test schemes in that
universe, rather than an independent potentially smaller test universe.
Coefficients and values are in u+1 as required by the source functors; ULift
supplies that universe without restricting the module dimension or cardinality.
No auto-implicit variable or unbound universe occurs.

Independent reuse searches made in this reading:

- LeanSearch via msearch: "base change isomorphism torsion abelian sheaves implies
  acyclicity injective finite field sheaves". Service unavailable (Internal Server
  Error); no mathematical verdict is inferred from that failure.
- LeanFinder via msearch: "vanishing higher direct images of pullback injective
  ZMod sheaf under proper base change". Eight hits: generic module-sheaf pullback
  identities, an affine-limit lemma, and derived-category injective Ext vanishing;
  none states this implication or either quantified property.
- Grep via msearch for ZMod and the property names found ordinary ZMod arithmetic.
  I additionally ran rg on Mathlib AlgebraicGeometry and CategoryTheory/Sites for
  the new property names, proper base change and injective/etale combinations:
  no relevant declaration. rg over project lean/Sheaf, source WeilConjectures,
  and `dag/lean_names_upstream.json` found the source module-valued forward
  theorem and the already landed canonical torsion definition. No exact forward
  theorem or duplicate of either new quantified property was found.

Mismatch and repair: H4 in the PBC dependency module. Its original `F.IsTorsion`
was mathematically equivalent local torsion, but was not the declaration recorded
by its torsion dependency. I replaced the Basic import with
`Sheaf.AlgebraicGeometry.TorsionEtaleSheaf` and used
`Scheme.IsTorsionAbelianSheaf F`; the dependency's lean.note records this choice.
This supersedes the Worker report's description of the original torsion binder.
The theorem signature, IA module, item statement, dependencies, and proof are
unchanged; both node lean.statement fields still equal their Lean signatures.

Docstring check: each module and declaration names its source and own blueprint
id. The theorem docstring follows all five node proof steps: torsion and the
specified exchange, module-injective direct-image acyclicity and degree zero,
exact inverse image and cohomology, transfer through the exchange and degree-zero
pullback, and universal conclusion. All named proof dependencies are retained.
There is exactly one delivered theorem and its proof is sorry; both definitions
have actual data. The imported torsion construction postpones only named proof
lemmas, which is allowed. Imports serve the declarations and all lines are at
most 100 characters. Compilation of all three modules together on the server
succeeded cleanly (1.9 seconds), with no errors or warnings.
