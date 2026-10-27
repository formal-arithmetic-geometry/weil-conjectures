## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEmbeddedDualNumberGraphs` states
`AlgebraicGeometry.FiniteEmbeddedDualNumberGraphs.classification`. Its only theorem
has proof `sorry`; every helper has real data. No statement correction is needed.
The recorded source was read in `literature/stacks-project/quot.tex`,
`remark-q-defos` (Tag 0CZV), lines 2133–2184: its subsheaf K'_phi is exactly the
graph relative to the trivial lift. The finite-support and coefficient formulas
are the explicit specializations in the node's nine proof steps; those steps
are included in the theorem's docstring.

Hypotheses, objects and clauses, in statement order:

- A field k is `{k : Type u} [Field k]`; X and Z are `Scheme.{u}`. The specified
  structure map is `f : X ⟶ Spec (.of k)`, with `[IsHProjective f]`. This is the
  recorded finite-projective-space embedding convention, not a properness substitute.
- The specified closed subscheme is `i : Z ⟶ X` with `[IsClosedImmersion i]` and
  `[IsFinite (i ≫ f)]`. Its ideal is precisely `i.ker`, and its O_X-module is the
  recorded `i.ker.toModules`. No arbitrary ideal, quotient or identification is assumed.
- A = k[epsilon]/epsilon^2 is `DualNumber k`. The theorem's first conjunct is
  `IsPullback X.dualNumbersProj (structureMap f) f (Spec.map ...inlHom...)`.
  Thus the existing `X.dualNumbers` is explicitly identified, compatibly with both
  projections, with X times_k Spec A. It has exactly the same topological space and
  section rings `DualNumber Γ(X,U)` by the definition in the existing source module.
- The linear maps are `TangentMap i`, definitionally O_X-module morphisms
  `i.ker.toModules ⟶ (Scheme.Modules.pushforward i).obj
  (SheafOfModules.unit Z.ringCatSheaf)`. This is i_*O_Z itself, not a chosen
  abstractly isomorphic module or an arbitrary quotient.
- `IsGraph i h J` is the displayed local condition on **every** open U and
  every dual-number section s: membership in `J.idealOfOpens U` iff there is an
  ideal section a with `i.ker.toModulesι.app U a = s.fst` and
  `i.app U s.snd = h.app U a`. The inclusion is injective and its range is the
  ideal, by the existing ideal/module bridge. This is exactly a in I and
  b mod I = h(a), including the sign convention in the node.
- `∃ F : TangentMap i → X.dualNumbers.IdealSheafData` together with
  `∀ h, IsGraph i h (F h)` gives the canonical graph assignment by its literal
  section formula. No object is chosen from a postponed existence theorem.
  `Function.Injective F` and the following range iff assert precisely bijectivity
  onto the required ideals. `IdealSheafData` is the existing quasi-coherent ideal
  representation. The range is `Flat (J.subschemeι ≫ structureMap f)` and
  `J.comap X.dualNumbersι = i.ker`: the quotient's closed subscheme is A-flat,
  and its reduction is the specified quotient, including the quotient map.
  Equality of ideals is stronger than an unmarked isomorphism of special fibres,
  as required by the word "specified" in the node.
- The degree clause is
  `((F h).subschemeι ≫ structureMap f).IsFiniteLocallyFreeOfDegree (degree f i)`.
  `degree f i` is the actual `Module.finrank k Γ(Z,⊤)` with scalars restricted
  along `(i ≫ f).appTop` and the canonical `Scheme.ΓSpecIso` inverse. The recorded
  degree predicate includes finite, flat, locally of finite presentation and the
  required degree at every point. No basis or finite-dimensionality assumption
  was added; those follow from the given finiteness.
- For **every** `U : X.Opens` and ideal J on `U.toScheme.dualNumbers`, the open
  clause says `IsOpenGraph i h U J ↔ J = (F h).comap U.ι.dualNumbers`.
  The helper is the same graph formula evaluated on the opens `U.ι ''ᵁ V`,
  transporting coefficients by `(U.ι.appIso V).inv`. Those are exactly the
  section maps of the restricted sheaf morphism; no affine, quasi-compact,
  finite-support or projectivity condition is imposed on U.
- For every `c : k`, the theorem specifies hc sectionwise as multiplication of
  h by the restriction to U of `f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)`.
  It asserts `F hc = (F h).comap (X.dualNumbersScale ...)`. This uses the
  canonical epsilon ↦ c epsilon substitution; c need not be nonzero.
- `TwoCoefficients k` is the explicit quotient of `DualNumber (DualNumber k)`
  by the mixed monomial epsilon_1 epsilon_2. The original two squares already
  vanish, so its ring is exactly k[epsilon_1,epsilon_2]/(epsilon_1,epsilon_2)^2.
  `twoAmbient f` is the pullback of the iterated dual-number model along this
  ring quotient, and `twoStructureMap f` is its second projection. In
  particular flatness is asserted over this square-zero ring, never over the
  iterated-dual-number ring with nonzero mixed monomial.
- The last clause specifies `d : X.dualNumbers ⟶ twoAmbient f` by
  `d ≫ twoAmbientι f = X.dualNumbersFold`. The closed immersion into iterated
  dual numbers makes this factorization unique. Since the existing fold sends
  both epsilons to epsilon and kills their product, this specifies the exact
  coefficient substitution, not an arbitrary map.
- For every h_1,h_2 the last clause produces an ideal J satisfying `IsTwoGraph`.
  That condition gives, on every open, the inverse-image ideal upstairs:
  a = s.fst.fst lies in I, s.fst.snd mod I = h_1(a), and
  s.snd.fst mod I = h_2(a). The mixed coefficient is unrestricted because
  it vanishes on the square-zero ambient scheme. This characterizes exactly
  the displayed two-parameter ideal on that ambient scheme. The conclusion
  includes `J.toModules.IsFlatOver (twoStructureMap f)` (literal ideal
  flatness), `Flat (J.subschemeι ≫ twoStructureMap f)` (flat quotient), and
  `J.comap d = F (h₁ + h₂)` (the required closed-subscheme pullback).

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsHProjective`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: `IsFinite`.
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic: `Scheme.Hom.ker`.
- Mathlib.Algebra.DualNumber: `DualNumber`, `DualNumber.eps`.
- WeilConjectures.AlgebraicGeometry.BaseChangeConventions: base-change
  convention `pullback f T.hom`, its `pullback.fst` and `pullback.snd`; the
  module also records `Scheme.Modules.moduleBaseChange`, which concerns module
  pullback rather than the ambient base change needed here.
- Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules` is definitionally
  `SheafOfModules`; the existing `Scheme.Modules` specializes this to X.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `Flat`.
- WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree:
  `Scheme.Hom.IsFiniteLocallyFree`, `Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module:
  `IdealSheafData.toModules`, `toModulesι`, `idealOfOpens` and the documented
  section-range comparison. The existing bridge is used without a private copy.
- WeilConjectures.AlgebraicGeometry.DualNumbers: `Scheme.dualNumbers`,
  `dualNumbersProj`, `dualNumbersι`, `Hom.dualNumbers`, `dualNumbersToSpec`,
  `dualNumbersScale`, `dualNumbersFold`.
- Mathlib.AlgebraicGeometry.IdealSheaf.Functorial: `IdealSheafData.comap`,
  the canonical ideal of the pullback closed subscheme (def-nagata-extended-ideal).
- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic:
  `Scheme.Modules.IsFlatOver` (def-pc-scheme-module-flat-over), needed for the
  literal ideal-flatness clause. The last two landed definition nodes were
  added to stmt_deps as authorized by brief-stage2 section 5.

The modules of all already-stated non-Mathlib proof dependencies are imported
privately: QuasicoherentCokernel, QuasicoherentKernel, AffineModuleCorrespondence,
AffineChartRelativeFlatCriterion, QuasiCoherentCokernelImage,
ThickeningAffineScheme, and FiniteFreeAlgebraSpectrum. The Mathlib leaves
(tilde adjunction and sections, field-module flatness, ring-map flatness,
closed subschemes, affine flatness) are available through these imports.
lem-sfb-nilpotent-ideal-module-flatness has no Lean record or Mathlib match;
it remains a proof prerequisite named in the complete natural-language proof,
and supplies no object needed to type this statement.

Edge cases checked mathematically before writing:

- Empty Z: I = O_X, the tangent-map space is zero, the graph is the unit ideal,
  the corresponding subscheme is empty and has degree zero. Empty X and empty
  restriction opens obey the same formulas. No nonemptiness binder is present.
- Z = X when X is finite: I = 0 and only the trivial ambient deformation occurs.
- h = 0 gives I plus epsilon I, the trivial embedded lift.
- Scalar zero gives that trivial graph by the generated ideal calculation;
  no invertibility, flatness or nonzero condition on scalar substitution is used.
- Characteristic two: square-zero two-parameter addition kills the mixed term
  by definition and never divides by 2. The coefficient quotient still has
  basis 1, epsilon_1, epsilon_2 over every field.
- Non-affine X and arbitrary non-affine/non-quasi-compact restriction opens are
  retained; graph conditions quantify over every open, not only affine charts.
- Universe u is explicitly bound for k and schemes, matching their ambient
  category; no test-algebra quantification can become vacuous. `autoImplicit`
  is disabled. The section module's field action is explicitly constructed.

Searches made:

- msearch.py leanfinder: "Flat embedded deformations of a closed subscheme over
  dual numbers correspond to linear maps from ideal sheaf to quotient" returned
  eight hits, headed by `IsClosedImmersion.overEquivIdealSheafData`; other hits
  include formally unramified morphisms, quotient lifts and the affine subscheme
  construction. None states the graph classification or its operations.
- msearch.py loogle: "DualNumber, Ideal" returned
  `DualNumber.maximalIdeal_eq_span_singleton_eps` and `DualNumber.ideal_trichotomy`.
  These describe ideals of the dual-number field, not embedded deformations.
- msearch.py grep: `graph.*(ideal|deform)|ideal.*graph` in AlgebraicGeometry
  returned zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for DualNumber, dualNumbers,
  TrivSqZeroExt and deformation graph names found the existing dual-number
  scheme, scalar and fold constructions, all reused. No graph classification.
  `grep -rn lem-sfb-finite-embedded-dual-number-graphs lean/WeilConjectures`
  returned no match. Searches for the new namespace and helper names returned
  no declaration. `blueprint_refs.py search embedded dual` returned zero nodes.

Validation: scompile.py compiled both the sandbox probe and the actual module
cleanly under the prescribed 60-second per-file limit (16.3 s and 9.8 s).
No warning or error remained. The only postponed theorem is `classification`.
No STATEMENT-DISPUTED flag or source fault was found.

## Second reading by Q74

A separate pass over the open node and the compiled file checked every clause
against the above translation. This is a self-review; the dispatcher explicitly
forbids starting another agent, so the maintainer's independent review remains
independent. No independent agent review is claimed here.

The main interface checks were: (i) use of the actual i_*O_Z rather than an
arbitrary quotient, (ii) reduction equality of ideals rather than only an
isomorphism of subschemes, (iii) all opens including non-projective open
subschemes, (iv) restriction of the scalar from global sections to U,
(v) the mixed monomial being zero in the two-parameter base, and (vi) flatness
of that ideal itself as well as its quotient. During compilation the scalar
formula was corrected to restrict the global scalar to U. The coefficient
monomial received its explicit type, and ring-map constructors were fully
qualified. The full source proof and all helper declarations were reread;
no hypothesis or conclusion was removed or added beyond the explicit
identification of the already-specified same-space ambient model.
