## Worker report

The module `Sheaf.Paper.CondensedFinitePresentationDescent` states
`AlgebraicGeometry.ProEtale.exists_constructible_finiteCoefficient_model`, with `sorry`.
No definition is introduced, no statement is corrected, and the only changed node field is
`lean`. The declaration docstring carries the seven steps of the node's proof.

Hypotheses and clauses, in order:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`; the base field is Mathlib's `ℚ_[ℓ]`.
- The fixed algebraic closure is `PadicAlgCl ℓ`, definitionally
  `AlgebraicClosure ℚ_[ℓ]` (Mathlib, NumberTheory/Padics/Complex.lean).
  Choosing this standard representative does not impose an extra mathematical hypothesis.
- The scheme is `(T : Scheme.{u})`. Its underlying topological space, rather than its
  structure sheaf, is noetherian: `[TopologicalSpace.NoetherianSpace T]`.
- `padicAlgClRingObj T ℓ` is precisely `p_T^*` of the finite-subextension-valued condensed
  ring. `Profinite.padicAlgClCondensedRing` is built from the subring of continuous maps
  whose values lie in one finite intermediate field, not all continuous maps to the closure.
- `M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ)` is an
  internal module sheaf with the specified ring action on the pro-etale site.
- `hM : IsConstructibleModuleObject (padicAlgClRingObj T ℓ) M` means there exists a finite
  scheme stratification on which the pulled-back module is pro-etale locally finitely
  presented. `IsLocallyFinitelyPresented` quantifies over a pro-etale cover and uses
  `Mod.IsFinitelyPresented`, the cokernel of a map of two finite-rank free modules.
  `Scheme.Stratification` additionally records constructibility of the locally closed
  strata; on a noetherian space every locally closed subset is constructible, as recorded
  by `Scheme.Stratification.ofNoetherianSpace`. Thus this adds no hypothesis to the node.
- The existential field is `E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)`, using the
  dependency's recorded declaration directly. This is definitionally the same subtype as
  the framework's `PadicAlgCl.FiniteIntermediateField ℓ`: intermediate fields with
  `FiniteDimensional ℚ_[ℓ] E.val`.
- The required coefficient sheaf is the existing `padicSubfieldRingObj T ℓ E`, namely
  `condensedRingObj (Profinite.continuousMapRingObj E) T`. It is determined by E and T,
  so no separate existential choice of this canonical sheaf is necessary.
- `M_E` is existentially quantified as an internal module over that coefficient sheaf;
  `IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) M_E` is its constructibility.
- `Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).obj M_E ≅ M)`
  asserts existence of an isomorphism in the algebraic-closure module category.
  This is the underived relative tensor product with its induced algebraic-closure action,
  not a bare isomorphism of underlying abelian sheaves or a derived statement.

Dependency declarations read and used:

- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`:
  `AlgebraicGeometry.ProEtale.IsConstructibleModuleObject`, `IsLocallyFinitelyPresented`.
  These are supporting declarations explicitly recorded by
  `def-weil-pbc-condensed-e-module-category`.
- The same dependency's module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`
  is publicly imported as required, though its base-change map is not used in this lemma.
  Its supporting `Basic` module defines `profiniteToProEt`, `pointUpperStar`,
  `upperStarFromPoint`, `condensedRingObj` and the coefficient comparisons.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`:
  `padicAlgClRingObj`, `padicSubfieldRingObj`, `padicSubfieldRingObjToPadicAlgCl`.
  They specialize the recorded condensed-coefficient construction without making copies.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`.
- Mathlib's `AlgebraicGeometry.Scheme`, `Padic`, `AlgebraicClosure` for the three remaining
  statement dependencies. Their definitions and docstrings were read in the pinned sources.
- `CategoryTheory.Mod.extendScalars` in the framework's `ModuleObjects.ExtendScalars`:
  relative tensor defined by the coequalizer of the two scalar actions.

The already stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.LocallyClosedStratification`,
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
The scheme-conventions node has no module or declaration to import. The already stated weakly-etale localization input is also imported without `public` as
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`. The other proof nodes have no
recorded Lean module at the immutable delivery commit.

Edge cases checked: the empty scheme and empty stratification are allowed; there is no
nonemptiness assumption on T. The zero sheaf has a zero model over the bottom finite field.
Presentation ranks may be zero. No reducedness, scheme-theoretic noetherianity, separatedness,
properness, or completeness condition is added. The conclusion allows the bottom field and
any larger finite field. The universe `u` is arbitrary; the module coefficients and abelian
sheaf category use the framework's `u + 1` convention.

Searches (2026-10-15):

- `msearch.py ... leanfinder "A constructible sheaf of modules over condensed algebraic
  closure of p-adic numbers descends to a finite intermediate field"`: 8 hits, concerning
  condensed free/solid module functors and field embeddings; none states this descent.
- `msearch.py ... loogle "IsConstructibleModuleObject, Mod.extendScalars"`: 0 hits;
  the project predicate is unknown to the Mathlib search service.
- `msearch.py ... grep 'constructible.*descen|exists.*[Cc]onstructible|finite.*[Pp]resentation.*descen'
  Condensed`: 0 hits.
- `rg` of `IsConstructibleModuleObject|exists_constructible_finiteCoefficient_model` and of
  this node id in the pinned upstream `WeilConjectures` and project `lean/Sheaf`: no exact
  descent theorem. Other constructible descent results concern discrete etale modules.
- `rg` in the exact 51-module pro-etale framework finds the constructibility definitions
  and the bounded derived object-descent theorem in `TwoColimit`, but no single-sheaf
  theorem with this signature. Derived object descent is a different statement.
- `rg` in `dag/lean_names_upstream.json` finds no candidate for the chosen declaration name.

No STATEMENT-DISPUTED flag or dependency fault was found. Validation is server-only through
`scompile.py`, with the dry-run delivery check to follow. No proof has been attempted.
The final module compiled cleanly through `scompile.py` (1.9 seconds for the item;
all required side-only framework files also passed their separate 60-second limits).
The first attempt required enabling the framework's existing `CategoryTheory.Obj` scope
to expose its ring-object instances; no statement change was needed.
The archived literature path is absent on this machine; the source reviewed is the exact
51-module framework copy identified by `coord/pefw-upstream-framework.md`.

## Second reading by NV

I read the node statement, its recorded dependencies, the upstream `TwoColimit.lean` (Obj)
descent paragraph, and the delivered module line by line. The correspondence is:

- The node's prime `ell` and fixed algebraic closure `Omega` are rendered by
  `(ell : Nat) [Fact ell.Prime]` and `PadicAlgCl ell = AlgebraicClosure Q_[ell]`.
- The node's scheme and noetherian underlying space are rendered by
  `(T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]`; no reducedness,
  separatedness, properness, or scheme-theoretic noetherian hypothesis is introduced.
- The node's finite-subextension-valued condensed coefficient ring and its pullback are
  rendered by `padicAlgClRingObj T ell`, using `padicAlgClCondensedRing` rather than all
  continuous maps to the closure.
- The Omega-module and its constructibility/local finite presentation hypotheses are
  rendered by `M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) ...` and
  `IsConstructibleModuleObject ... M`. Its definition supplies a finite
  `Scheme.Stratification` and `IsLocallyFinitelyPresented`, whose finite presentation is
  `Mod.IsFinitelyPresented` by a map between finite-rank free modules.
- The existential finite field `E` is rendered by
  `Padic.FiniteCoefficientFields ell (PadicAlgCl ell)`, exactly the finite intermediate
  fields in the recorded dependency. The coefficient sheaf is the canonical
  `padicSubfieldRingObj T ell E`; no extra choice is introduced.
- The model, its constructibility, and the comparison are rendered respectively by
  `M_E`, `IsConstructibleModuleObject (padicSubfieldRingObj T ell E) M_E`, and
  `Nonempty ((Mod.extendScalars (...)).obj M_E ≅ M)`. `extendScalars` is the internal
  underived relative tensor product with the induced algebraic-closure module action.
  The conjunction and quantifier order agree exactly with the node.

No mismatch was found, so no repair was needed. In particular, the Lean statement does
not add a nonempty scheme or stratum, excludes no zero module, and permits the empty
stratification, rank zero, and the bottom coefficient field. The arbitrary universe `u`
and the `u+1` abelian-sheaf convention preserve the node's universe cases.

I searched LeanFinder, Loogle, LeanSearch, grep over the pinned upstream project and
Mathlib, grep over the exact 51-module pro-etale framework and `lean/Sheaf`, and the
upstream-name index. No declaration states this single-sheaf finite-coefficient descent;
the nearby two-colimit theorem is a different derived-category statement. LeanSearch was
unavailable, while the other searches returned no exact match. The module compiles by the
required server `scompile.py` check with only the permitted `sorry` declaration warning.

The dependency chain was checked through `ProEtaleModule/Def`, `ModuleObjects/Free`,
`ModuleObjects/ExtendScalars`, `ModuleObject/Basic`, `Colimit/Compatibility`, condensed
`EllAdic` and `FiniteSubextension`, and the recorded `FiniteCoefficientFields` module.
`Scheme.Stratification.ofNoetherianSpace` confirms that its constructible-subset field
adds no restriction here: every locally closed subset of a noetherian space is
constructible. `PadicAlgCl` is the recorded standard fixed algebraic closure, not its
completion. `PadicAlgCl.FiniteIntermediateField` and `FiniteCoefficientFields` unfold to
the same subtype. There are no new nodes or dependency modules to review, and no
`statement_change`, so there are no corrected-statement citers to audit.

Independent search queries were LeanFinder “finite field model for constructible sheaf
over algebraic closure with continuous coefficients” (eight irrelevant prime-spectrum
constructibility hits), Loogle `Mod.IsFinitelyPresented` (unknown to the Mathlib service),
and LeanSearch “A constructible condensed module over the algebraic closure of Q_l
descends to a finite extension of Q_l” (service unavailable). Grep patterns included
`finiteCoefficient.*model`, `constructible.*coefficient.*descent`, the exact theorem name,
and `descen|essSurj` in `TwoColimit.lean`. I also checked the declaration docstring's
seven proof steps against the node, its source label, permitted imports and 100-character
line widths. The only proof is `sorry`; there is no new data definition, local notation,
local instance, hidden binder, or extra axiom. The node's `lean.statement` matches the
source signature verbatim.


### Maintainer import correction

The independent maintainer review found H9: at delivery commit
`65f8f71e846e58ccea4080644baa1ffdcc177fc2`, proof dependency
`lem-weil-proetale-weakly-etale-localization` already recorded
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, but its required proof-only
import was missing. Added that import. The theorem signature, node and mathematical
statement are unchanged. The earlier second-reading claim about permitted imports
missed this dependency; the correction above supersedes it.

The complete replacement module passed the server-only `scompile.py` check with exit 0
(item 1.9 s; localization dependency 2.7 s; all side-only imports passed, maximum
44.9 s), nice 19, two threads and 60 seconds per file. No errors or warnings were
reported. The signature remains verbatim equal to the node record.
