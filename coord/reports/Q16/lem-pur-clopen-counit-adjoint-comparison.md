## Worker report

The module `Sheaf.Paper.ClopenCounitAdjointComparison` states the two parts of
`lem-pur-clopen-counit-adjoint-comparison` as
`WeilConjectures.PurityFiniteSetting.clopenCounitAdjointComparison_finite` and
`WeilConjectures.PurityFiniteSetting.clopenCounitAdjointComparison_system`.
Both proofs are `sorry`; the seven helper definitions have actual data. The node's
statement and proof are unchanged. One existing landed definition dependency,
`def-pur-clopen-strict-system-comparison`, is added for `clopenSystemRing` and
`clopenSystemUniformizer`. No new nodes are needed. The support dependency is repaired under §1(B), as detailed below; the landed scalar-image definition node is also cited.

Source read: Zheng, arXiv:1006.3810, Construction 5.15, Lemma 5.16 and the Brown
right-adjoint paragraph following it, and Lemma 5.22, printed pp. 34–36. Also read
the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md`.
The clopen assembly is the seven-step argument retained in the DAG proof, rather
than a claim that Zheng prints this assembled statement verbatim.

Hypotheses and clauses, with the node and Lean file open:

* The finite field, prime different from its characteristic, finite extension,
  integers, fixed uniformizer, and positive finite level are the existing
  `P : PurityFiniteSetting.{u}` and `P.Ring`. `P.level_pos` is passed to every
  intrinsic bounded constructibility predicate. The two scheme structure maps
  are `X Y : Over (Spec (.of P.field.k))`. Their finite-type conditions are each
  `LocallyOfFiniteType` plus `QuasiCompact`; the same two conditions and
  `IsSeparated` apply to `g.left`. There is no separatedness assumption on Y.
  An `include` explicitly retains these hypotheses even when not needed for
  elaboration of the displayed categorical formula.
* `I : Type w`, `[Finite I]`, the `Xi`, `j`, open and closed immersion instances,
  `hdisjoint`, and `hcover` give exactly the finite clopen cover. The latter two
  are explicitly included in the finite theorem. Component finite-type and
  separatedness facts are consequences of `clopenSupport_geometry`, not extra
  assumptions. The system theorem repeats the same geometry using `sY` and
  `g ≫ sY`, with explicit disjointness and cover arguments.
* The common compactification is `c`; each component uses `c.precomp (j i).left`
  (or `c.precomp (j i)` in the system clause). Restriction is the existing
  `Scheme.sfIntrinsicDerivedPullback`, insertion is `sfIntrinsicDerivedOpen`,
  and `b` is `P.clopenSupportComponentComparison`. The finite conclusion supplies
  `adj` with its unit equal to `sfIntrinsicDerivedOpenUnit`, fixing the specified
  insertion adjunction, rather than introducing an arbitrary insertion map.
* `ProEtale.sfFiniteExceptional` is the existing finite exceptional functor in
  intrinsic constant-ring coordinates. `clopenCounitEtaleRight` and
  `clopenCounitEtaleAdjunction` expose its ordinary etale right adjoint and the
  canonical compactification transport. `clopenFiniteCounit` is the actual
  composite of the intrinsic support comparison, the D+ etale/pro-etale support
  comparison, the etale adjunction counit, the comparison-site counit, and the
  intrinsic coefficient equivalence counit. Its `ClopenCounitBound` witness is
  concluded by `hG` and `hGi`, for every compactification and constructible L;
  it is not an added hypothesis. Thus this is the finite etale-origin counit,
  not an assumed ambient pro-etale right-adjoint counit.
* The explicit constructibility conjunct asserts that `G_g L`, `r_i G_g L`,
  and `G_gi L` belong to the corresponding full bounded constructible categories.
  `rho` is a natural isomorphism with source the inclusion of the full
  constructible input category followed by `G_g` and restriction. Fullness
  identifies its components and their Homs with those in D^b_c; the ambient
  target notation does not enlarge the allowed input category.
* `∃! rho` gives existence and uniqueness. Its first equation is exactly
  `F_gi.map (rho.hom.app L) ≫ epsilon_gi = b.inv ≫ F_g.map insertionCounit ≫
  epsilon_g`, in Lean's left-to-right composition notation.
* The `Function.Bijective` clause is the natural represented Hom chain, written
  as one composite map: apply `F_gi` to a component arrow, then `b.inv`, then
  compact support of the insertion counit, then the exceptional counit.
  This is the insertion transpose followed by the exceptional transpose;
  composition and the natural transformations used in this expression supply
  its naturality in both full-subcategory objects M and L. Composing rho with
  the component exceptional transpose gives this very map by its counit
  equation, so the statement fixes the represented bijection, not merely the
  cardinalities of its Hom sets.
* The support-sum component in `clopenSupportSumIso` is the inverse of `b`
  followed by support of the inclusion counit, the same factors appearing in
  the equation and Hom map. Thus this equation specifies the component
  right-adjoint comparison of that finite sum. The equation and Hom bijection
  quantify over every `d : Compactification g.left`; the fixed exceptional
  functor is definitionally independent of the compactification proof instance.
  Together with `clopenSupportCanonicalComparison`'s etale normalization, this
  expresses compatibility with every canonical compactification comparison.
* The system clause uses the actual `DerivedCategory
  (strictEtaleCoefficientSystem ...)`, not a category of sequences in a derived
  category. The coefficient ring is the existing `clopenSystemRing` (a universe
  lift of O), with `clopenSystemUniformizer`. `S`, `Si`, `R`, `D`, `B` are precisely
  the existing strict-support data; `G` and `Gi` are the actual adjoints from
  `StrictEtaleExceptionalAdjoint`. Their records include ordinary and derived
  normalization and evaluation coherence, so no arbitrary substitute functor
  or mere existence choice is used.
* `clopenSystemComponentCounit` is `B.support.inv`, then support applied to
  `D.reverseAdj.counit`, then `G.adjunction.counit`. The first two system
  conjuncts assert the same counit equation and uniqueness among all natural
  isomorphisms satisfying it. The next conjunct states commutation of rho with
  the derived O-scalar action. The functors are additive and O-linear by the
  existing adjoint and restriction records; the displayed scalar equation makes
  their comparison O-linear on morphisms.
* `∃ rhoLevel : ∀ n : ℕ, ...` binds all finite comparisons together. For each
  n the first family clause is the finite counit equation formed with
  `B.levelSupport`, `D.reverseLevelAdj`, and `G.levelAdjunction`; the second
  clause says every isomorphism satisfying that equation equals `rhoLevel n`.
  The third clause identifies evaluation of rho with `rhoLevel n` via
  `D.image.inverseEvaluation`, `G.evaluation`, and `Gi.evaluation`, retaining
  exactly the existing `B.sameTarget` transport.
* The last clause now quantifies over every `L : D(strictEtaleLevel Y O ell m)`,
  and compares scalar extension of `(rhoLevel m).hom.app L` followed by
  `Gi.quotientComparison h` with `clopenRestrictionQuotient ... h` at `G_m L`,
  restriction of `G.quotientComparison h`, and `(rhoLevel n).hom.app (scalar L)`.
  The final `eqToHom` transports the identical target scalar package using
  `B.sameTarget`. The restriction mate is `(D.scalar i).derivedTensor.symm`,
  with its ordinary tensor-unit and flat-term K-flat representative equations.
  Thus both prescribed exceptional quotient mates occur on arbitrary finite
  objects. The rejected formula was only naturality of the evaluated system
  map plus Gi's transition coherence; that formula has been removed.

Dependency interfaces used (module and declarations):

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Ring`, `Coefficient`, and its prime/finite instances.
* Mathlib `AlgebraicGeometry.Morphisms.Proper`, `FiniteType`, `QuasiCompact`,
  `OpenImmersion`, `Morphisms.ClosedImmersion`: `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`, `IsClosedImmersion`.
* `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`
  and its category; the common compactification and `precomp` are the existing
  compactification API used by its recorded declaration.
* `Sheaf.Paper.ClopenCommonCompactSupport`: `clopenSupportComponentComparison`,
  `clopenSupport_insertion`, `clopenSupport_restriction_constructible`,
  `clopenSupportSumIso`, `clopenSupportCanonicalComparison` and coherence.
* `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: recorded
  `ConstructibleExceptionalCoefficients.System` and publicly imported finite
  interface `ProEtale.sfFiniteExceptionalAt`; its intrinsic realization is the
  existing `ProEtale.sfFiniteExceptional` in
  `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`. The latter uses
  exactly the etale adjoint, comparison Rnu and Dnu, and coefficient realization.
* `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`:
  `ProEtale.specifiedExceptionalHomEquiv`; its comparison dependencies supply
  `fixedCompactSupportComparisonIso` and `derivedComparisonAdjunction`.
  `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange` supplies
  `sfIntrinsicCompactSupportComparison`.
* `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`; Mathlib
  `AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
* `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `Scheme.sfIntrinsicCompactSupport` and its canonical coefficient realization.
* `Sheaf.Paper.ClopenStrictSystemSupport`: `StrictEtaleClopenOrdinary`,
  `StrictEtaleClopenDerived`, `StrictEtaleClopenSupport`,
  `clopenStrictSystemSupport`, especially image, reverseAdj, reverseLevelAdj,
  inverseEvaluation, support, levelSupport and sameTarget.
* `Sheaf.Paper.EtaleCoefficientSystemAdjoint`: `StrictEtaleCompactSupport`,
  `StrictEtaleExceptionalAdjoint`, `etaleCoefficientSystemAdjoint`,
  `strictEtaleCoefficientSystem`, `strictEtaleLevel`, scalar actions,
  evaluation, quotientComparison and the actual strict transitions.
* `Sheaf.Paper.CoefficientSystemImageData`: `SheafOfModules.CoefficientScalarImage`,
  including `tensor_unit`, `derivedTensor`, `derivedTensor_rep`, and the
  restricted-image mate equations, retained by the repaired support interface.
* `Sheaf.Paper.ClopenStrictSystemComparison`: `clopenSystemRing` and
  `clopenSystemUniformizer`, reused instead of defining a second O lift.
* Mathlib `CategoryTheory.Adjunction.Unique`, `Basic`, `Mates`:
  `Adjunction.rightAdjointUniq`, composite adjunctions, and mates. The finite
  clopen constructible decomposition is already publicly imported by the
  common-support module. The theorem docstrings explain precisely how these
  proof dependencies assemble the comparisons; no proofs are supplied here.

Edge cases read against the displayed formula: a singleton identity component
has the identity normalized comparison; two components use the two inclusions
of the same support sum. Empty components have zero module categories, so the
Hom bijection and both counit equations are the unique zero maps. For empty I,
covering forces empty X and there is no indexed comparison. No nonempty instance
on I or Xi is introduced. `P.level_pos` includes n=1, with no flatness condition.
All strict-system levels (including their API's level zero), all quotient
inequalities, identity quotients and successive quotients remain quantified.
The coefficient/site universes are the published intrinsic finite interface and
the published O : Type (u+1) strict-system interface; no new universe equality
is assumed. No ambient unbounded pro-etale adjunction is asserted.

Searches performed, using the launcher's `msearch.py` and repository reads:

* LeanFinder: `Restriction of exceptional right adjoints to clopen components has a unique counit normalized comparison compatible with evaluation of strict coefficient systems`.
  Eight hits concerned `CompHausLike.LocallyConstant` adjunctions, not this result.
* Loogle: `CategoryTheory.Adjunction.rightAdjointUniq`. Twelve hits gave generic
  uniqueness and its counit and transitivity formulas, reused rather than copied.
* Mathlib grep: `rightAdjointUniq|clopen` in `CategoryTheory/Adjunction`.
  Six hits in Unique and Triple give generic adjunction results only.
* LeanSearch: `clopen restriction exceptional right adjoint counit comparison`.
  Eight hits concerned comonadicity/monadicity comparison counits and ordinary
  restriction/coextension of module scalars. None has the finite constructible
  and actual strict-system clauses of this node.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for clopen/counit/exceptional
  comparisons, and the exact node id in `lean/WeilConjectures`: no existing exact
  statement. Existing clopen transfer and composite-counit normalization results
  concern other presentations or individual ingredients. The published broader
  finite-clopen restriction result includes additional descent/transport claims;
  it is not an exact existing-declaration attachment for this node. Existing
  coefficient lifts and canonical comparisons were reused.

## Dependency modules

`lem-pur-clopen-strict-system-support`, module
`Sheaf.Paper.ClopenStrictSystemSupport`: the recorded `StrictEtaleClopenDerived`
only retained `CoefficientEvaluationImage`, so it could express evaluation but
could not provide the canonical quotient restriction mate required by the node's
transition clause and proof Step 6. Its `StrictEtaleClopenDerivedData` now retains
`scalar : ∀ i, CoefficientScalarImage ... (image i)` on the same fixed evaluation
images. This is the existing coefficient scalar interface, with actual ordinary
tensor isomorphisms, ordinary unit normalization, derived tensor isomorphisms,
K-flat representative equations, and restriction/direct-image mate equations.
The clopen existence theorem still states the same geometric decomposition and
support comparison; its proof plan now explicitly retains this part of
`coefficientSystemUnboundedComparison`. Only the dependency's `lean` record is
changed. All its original declarations are retained. No extra geometric,
coefficient-flatness, or universe hypothesis is introduced.

## Return repair H3

Compared the retained packet with the current published support interface. The
returned theorem had not been repaired: its last conjunct used only Gi and the
actual transition's naturality. Replaced it by the requested square on arbitrary
level objects, after binding one family `rhoLevel`. The counit equation,
per-level uniqueness, evaluation identity, and all finite and system geometry
clauses remain. The sole added helper `clopenRestrictionQuotient` has real data:
it is the inverse of the normalized derived tensor comparison from the repaired
support interface. The owning landed node `def-pur-coefficient-system-image-data`
is cited alongside the already cited `def-pur-clopen-strict-system-comparison`.

The existing `ClopenCounitComparison` and `StrictClopenExceptionalComparison`
records were read. They package precisely the same normalization and evaluation
conditions, but their derived restriction uses a full `CoefficientSystemDerivedImage`
with descent fields. The support node supplies an evaluation image with the
clopen insertion adjunction instead. This delivery neither creates replacement
comparison record types nor changes those records: it states the requested
existence/uniqueness and writes the composite counit arrows explicitly. The
existing comparison and coefficient ring definitions remain imported and cited.
The O ring lift and dependency-existence theorem universes are unchanged from the
reviewed packet; the repair supplies no new equality between universes.

## Second reading by Q16

This is a self-audit by the assigned worker; the dispatcher forbids additional
agents and the independent maintainer review follows delivery. Read the current
node and both delivery modules together. The finite theorem is unchanged from
the accepted clauses of the return: finite coefficients, nonseparated target,
finite clopen cover including empty cases, pinned insertion unit, inverse b,
etale-origin counits, the unique normalized rho and represented Hom bijection.
The system theorem keeps its geometric hypotheses, actual derived strict systems,
specified counit composite and uniqueness, and O-scalar equation. The level
comparisons are now one family rather than independent existential scopes.
Each has the same counit equation, uniqueness and evaluation identity. The final
square has source scalar(r_m G_m L) and target Gi_n(scalar L). Its left side
uses rhoLevel m and Gi's prescribed mate; its right side uses the canonical
restriction mate, G's prescribed mate and rhoLevel n. The only transport is
`B.sameTarget.symm` on the target scalar package. Identity and successive
quotients remain quantified; no statement is reduced to evaluated systems.
The dependency scalar data is the existing normalized interface on exactly
D.image, so there is no arbitrary substitute morphism. Empty I and components,
level n=0 (positive exponent one), all quotient inequalities and nonseparated Y
remain admitted. The node's mathematical statement and proof are unchanged;
no statement correction or new node is needed.

Validation: `scompile.py Q16 lem-pur-clopen-counit-adjoint-comparison` compiled
both modules separately in dependency order, in sandbox and library-name modes.
The final library compiles took 29.8 seconds (support) and 54.3 seconds (item),
within the unmodified 60-second limit. No errors or extra warnings. The temporary
profiler option was removed. All universes and variables are explicit; both
postponed item theorems and the dependency existence theorem retain `sorry`.
The final `deliver2.py --no-push` passed server preflight and both per-file
compiles (dry-run commit 2251ec8824c). Node JSON changes were checked against
the current read clone: item only `lean` and `stmt_deps`, dependency only `lean`.
Both primary `lean.statement` fields match their file signatures verbatim.

Repair searches: `rg` of both project roots found the existing comparison records
in `ClopenStrictSystemComparison`; their full signatures and coherence were read.
`rg` found the existing `CoefficientScalarImageData.derivedTensor` and its
representative normalization in `CoefficientSystemImageData`, reused here.
A Loogle query for `SheafOfModules.CoefficientScalarImage` returned unknown
identifier (the service indexes Mathlib); the local source supplies the exact
existing project interface, so no scalar comparison is redefined.
