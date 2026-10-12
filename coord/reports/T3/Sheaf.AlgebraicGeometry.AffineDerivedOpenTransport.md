## What changed

Closed AlgebraicGeometry.affine_derived_open_transport without changing its signature or its existing docstring. The proof constructs the module and derived equivalences, identifies pushforward with restriction along a.inv, transports quasi-coherence and perfection using the existing lemmas, proves stalk-vanishing transport, supplies CommShift, and constructs the open adjunctions with matching units.

Added three modules, each with one public theorem and a complete Lean proof: SchemeIsoDerivedLocalizations, SchemeIsoDerivedRestrictionSquare, and SchemeIsoDerivedOpenAdjunction. Their private helpers are proved; every equivalence and localization is an explicit construction. No data is chosen from an unproved existence theorem.

Added proof imports for these modules, SchemeIsoDerivedQCoh, SchemeIsoPerfectTransport, the source exact-derived-functor API, and Mathlib adjunction uniqueness. Updated the original DAG proof and dependencies. No existing public interface changed and no other existing module was adapted.

Validation: all four sandbox modules compile in import order without warnings, each well within the single-file limit. The statement-diff check reports no signature change. The restriction square and adjunction proofs have no quasi-coherence, perfection, compactness, affineness or nonempty-point hypotheses. Empty schemes and empty/full opens are covered by the same constructions.

## Proved and sorry left

Closed 1 original hole: AlgebraicGeometry.affine_derived_open_transport (lem-pc-affine-derived-open-transport). Added 0 holes. No sorry remains in any delivered module.

Also proved AlgebraicGeometry.Scheme.exists_scheme_iso_derived_localizations (lem-pc-scheme-iso-derived-localizations), AlgebraicGeometry.Scheme.exists_scheme_iso_derived_restriction_square (lem-pc-scheme-iso-derived-restriction-square), and AlgebraicGeometry.Scheme.exists_scheme_iso_derived_open_adjunction (lem-pc-scheme-iso-derived-open-adjunction).

The original theorem uses the existing holed AlgebraicGeometry.Scheme.scheme_iso_derived_inverse_preserves_perfect (lem-pc-scheme-iso-perfect-transport), which is not changed in this delivery. This is a proof from an existing stated dependency, not a claim that the target import closure is sorry-free. The existing quasi-coherence transport theorem is already proved.

## No longer needed

Removed the direct proof import Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral. The exact-left-adjoint derived adjunction avoids the tensor-pullback construction. The following complete list is the difference between the old and new import closures of this item (other targets or items may still use them):

- Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral: lem-pc-ringed-spaces-derived-adjoint-general
- Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute: lem-pc-ringed-space-tensor-pullback-absolute
- Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux: q3-ringed-space-tensor-pullback-absolute-postcomposition, q3-ringed-space-tensor-pullback-left-derived
- Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived: lem-pc-ringed-space-tensor-pullback-underived

The foundational DerivedCategory and PerfectComplex nodes remain needed. No unused proof-dependency import was added.

## Where the brief, the DAG or earlier work was wrong

The planned general ringed-space tensor-pullback adjunction is unnecessary for exact open restriction. The existing source-library mapDerivedCategoryRightDerivedAdjunction gives its unbounded right adjoint directly. The isomorphism restriction square follows from overFunctorEquiv, restrictFunctorComp, restrictFunctorCongr and preimageIso_inv_ι; it does not require a new holed transport assumption.

The old proof dependencies listed only definitions for the geometric-transport step, although reusable scheme-isomorphism quasi-coherence and perfection declarations exist. These are now explicitly cited and imported. Tag 09IR is the affine Koszul detector lemma, not a standalone scheme-isomorphism transport theorem; the transport comparisons here are proved formally from the localization and restriction APIs. The new proof origins are marked agent rather than claiming verbatim proofs of Tag 09IR. The Stacks source files and blueprint unit page are not materialized on this machine; the unit record was read, and the cited Tags 05RU, 079W and 09IR were checked online.

The small ringed-site theorem prop-pur-kinjective-resolutions-exist is used as a generic tool in the new open-adjunction node, outside this unit. It already underlies the planned derived adjunction and supplies exactly the Grothendieck/K-injective structure needed. The maintainer may record this generic tool use; no unit statement or realized unit step was bypassed.

Searches used LeanFinder, Loogle and source rg; LeanSearch returned Internal Server Error. The search results and unavailable service are recorded in the new nodes.

## New nodes

- lem-pc-scheme-iso-derived-localizations: proven existence of localizations with the same morphism universe, on the scheme and all opens; strictly the localization-existence part of step 1.
- lem-pc-scheme-iso-derived-restriction-square: proven natural square for arbitrary isomorphism-induced derived equivalences, with no geometric-property or adjunction conclusion; strictly the restriction comparison of step 1.
- lem-pc-scheme-iso-derived-open-adjunction: proven construction of both adjunctions and the unit comparison from the restriction square and K-injective derived adjunction; strictly step 2.

No change record is needed: existing signatures, definitions and public imports are unchanged.

## Second reading by T3

1. Compared the delivered affine transport module with the repository version. The target
   signature and all existing declarations are unchanged; the three added declarations are
   separate new nodes, with no accidental edits outside the delivery.
2. Compiled all four modules in import order with `lcompile.py`; they compile without errors
   or warnings. Searched the delivered Lean files for `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, and `extern`; none occur. The proofs use only the permitted foundational
   axioms (apart from any pre-existing imported holes).
3. Checked each new node against its theorem. The localization, restriction-square, and
   open-adjunction statements are true constructions, strictly narrower than the target, and
   their docstrings give complete proof explanations. No duplicate declaration was found in
   the existing Lean library.
4. Reviewed the proof route and imports. The target uses the new localization and adjunction
   lemmas, existing QCoh/perfection transport, and exact derived-category APIs; the former
   tensor-pullback and general-adjunction imports are removed. The unit route remains through
   localization, restriction comparison, and derived open adjunction, including the recorded
   K-injective resolution dependency.
5. Checked the DAG proof steps, `proof_deps`, origins, and realized unit route against the
   Lean proof. The target closes one hole and adds no sorry; the three infrastructure nodes are
   proved and have matching Lean records.

I changed only this report section; no Lean proof or node content required repair.
