## Worker report

The module `Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair` states
`AlgebraicGeometry.exists_flatification_horizontal_curve_pair`. Its only theorem has
proof `sorry`; there are no new definitions, additional axioms, or postponed helper
statements. The node's mathematical statement and proof are unchanged.

I read the item, all seventeen original statement dependencies and their recorded
interfaces, the published strict-transform and admissible-blowup APIs, and the proof
modules imported by the delivery. The upstream Projective and RelativeProj.Basic modules
were read using `scompile.py --source` because the older local source tree lacks them.
The existing H-projectivity interface supplies exactly finite-projective-space
projectivity; it is distinct from `IsProjectiveBundle` throughout this theorem.

Source check: ILO, Expose X, proof of Theorem 3.4, Step 2, printed p. 160 (PDF page 166),
flattens the curve and horizontal boundary by a projective modification. I also read the
local Stacks statements and proof of Tag 081R (`flat.tex`, lemma-flat-after-blowing-up),
and Tag 0GSJ (`more-morphisms.tex`, lemma-flat-associated-equidimensional). The item makes
the consequences for a projective generic curve explicit. The module docstring gives
all eight proof steps, with the item’s dependency ids, for stage 3.

Hypothesis and conclusion matching (write `v = B.I.blowupMap`,
`p = c₁ ≫ pullback.fst h v`, `f = c₁ ≫ pullback.snd h v`, and
`q = i₁ ≫ c₁ ≫ pullback.snd h v` only as explanatory names here):

| Node clause | Lean rendering |
| --- | --- |
| Integral Noetherian base S | `[IsIntegral S] [IsNoetherian S]` |
| Excellent base | `hexc : ∀ V : S.Opens, IsAffineOpen V → IsExcellent Γ(S, V)` |
| Its generic point eta | `η : S`, `hη : IsGenericPoint η (Set.univ : Set S)` |
| Projective h:C→S, finite-projective-space convention | `h : C ⟶ S`, `[IsHProjective h]` |
| Integral C | `[IsIntegral C]` |
| Smooth irreducible generic curve of dimension one | `[Smooth (h.fiberToSpecResidueField η)]`, `[IrreducibleSpace (h.fiber η)]`, `hdim : topologicalKrullDim (h.fiber η) = 1` |
| Closed generic marking | `jη : Hη ⟶ h.fiber η`, `[IsClosedImmersion jη]` |
| Finite etale over the generic field | `[IsFinite (jη ≫ h.fiberToSpecResidueField η)]` and `[Etale (jη ≫ h.fiberToSpecResidueField η)]` |
| H is its schematic closure in C | `i : H ⟶ C`, `[IsClosedImmersion i]`, `hclosure : i.ker = (jη ≫ h.fiberι η).ker` |
| One blowup S1→S with centre away from a dense open | Existential `U : S.Opens`, `B : IsAdmissible S U`, `Dense (U : Set S)`; S1 is the actual `B.I.blowup` and v its actual blowup map |
| Centre is finite type and restricts to the unit ideal over U | The fields `B.finiteType` and `B.disjoint_support` of the existing admissible-blowup definition |
| Integral, Noetherian, excellent S1 | `IsIntegral B.I.blowup`, `IsNoetherian B.I.blowup`, and excellence of every affine coordinate ring |
| Projective-bundle v | `IsProjectiveBundle B.I.blowupMap` |
| Birational v | `IsIso (B.I.blowupMap ∣_ U)` with U dense; the integral source makes its nonempty inverse image dense as well |
| C1 closed in C×S S1 | `c₁ : C₁ ⟶ pullback h v`, `IsClosedImmersion c₁` |
| H1 closed in C1 | `i₁ : H₁ ⟶ C₁`, `IsClosedImmersion i₁` |
| The actual two strict transforms | `c₁.ker = (strictTransformι h v B.I.support.compl).ker` and `k₁.ker = (strictTransformι (i ≫ h) v B.I.support.compl).ker`, with `IsClosedImmersion k₁` |
| Both ambient inclusions describe the same H1 | The two projection equations for `k₁` identify its composite into C×S S1 with `i₁ ≫ c₁`. Thus k₁ is the canonical inclusion into H×S S1, with both projections specified |
| C1 is the schematic closure of C_eta×S S1 in C×S S1 | `c₁.ker = (pullback.snd (h.fiberι η) (pullback.fst h v)).ker` |
| H1 is the schematic closure of H_eta×S S1 in the same ambient scheme | `(i₁ ≫ c₁).ker = (pullback.snd (jη ≫ h.fiberι η) (pullback.fst h v)).ker` |
| Integral C1 | `IsIntegral C₁` |
| Projective, flat, finitely presented C1→S1 | `IsHProjective f`, `Flat f`, `LocallyOfFinitePresentation f`; H-projective implies proper, hence quasi-compact and quasi-separated, giving finite presentation |
| Every geometric curve fibre is nonempty and pure dimension one | For every `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, and `s : Spec (.of Ω) ⟶ B.I.blowup`, the pullback of f is nonempty and every irreducible component has `topologicalKrullDim = 1` |
| Finite, flat, finitely presented H1→S1 | `IsFinite q`, `Flat q`, `LocallyOfFinitePresentation q`; finiteness supplies the quasi-compactness and quasi-separatedness needed for finite presentation |
| Every nonempty geometric marking fibre has pure dimension zero | The same quantifiers for q, with `Nonempty (pullback q s) →` and dimension zero on each irreducible component |
| The original generic fibres are retained | Existential `gC : h.fiber η ⟶ C₁`, `gH : Hη ⟶ H₁` and the two `IsPullback` squares over `S.fromSpecResidueField η` |
| The generic-fibre identifications preserve the specified inclusions | `gC ≫ c₁ ≫ pullback.fst h v = h.fiberι η` and `gH ≫ i₁ = jη ≫ gC` |
| C1→C is proper and birational | `IsProper p` and `∃ V : C.Opens, Dense (V : Set C) ∧ IsIso (p ∣_ V)`; C and C1 are integral |
| Blowup means relative Proj of the Rees algebra | The existing `B.I.blowup` glues `AffineBlowup (B.I.ideal V)`; `AffineBlowup` in upstream `Blowup/Affine/Defs.lean` is `Proj (reesGrading I)`. This is the relative Proj of the powers I^n, not an unspecified birational map |
| Schematic closure means kernel of restriction | All closures use the existing `Scheme.Hom.ker` and closed-subscheme interface. On the quasi-compact maps here, `Hom.ker_apply` identifies this ideal with the kernel of the map on sections |

The pullback used in the curve closure formula has source
`C_eta ×_C (C ×_S S1)`, canonically `C_eta ×_S S1`; the marking formula similarly has
source `H_eta ×_C (C ×_S S1)`, canonically `H_eta ×_S S1`. Thus the formulas use exactly
the ambient scheme in the node. Equality of kernels of two closed immersions identifies
their closed subschemes up to the unique isomorphism over that ambient scheme. It does
not merely identify their topological supports. The auxiliary schemes and maps in the
existential are these specified closed subschemes and their canonical structure maps.

There is no additional generic-point equality or arbitrary residue-field isomorphism:
the two generic squares are pullbacks over the original S, and the actual blowup is an
isomorphism on the dense U containing eta. They therefore identify the generic fibres
also over the corresponding generic point of S1 and its canonically identical field.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`, built from
  locally Noetherian coordinate rings (`IsNoetherianRing`) and compactness.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, applied to affine coordinate rings.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `AlgebraicGeometry.IsHProjective`;
  `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `AlgebraicGeometry.IsProjectiveBundle`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`; `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `.Etale`, `.Flat`, `.Finite`,
  `.FinitePresentation`, `.Proper`: the recorded `Smooth`, `Etale`, `Flat`, `IsFinite`,
  `LocallyOfFinitePresentation`, `IsProper` predicates.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: the closed-subscheme and kernel
  interface, including the recorded `Scheme.Hom.image`; image is `f.ker.subscheme`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`;
  `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`: canonical relative Proj,
  `Scheme.GradedAlgebraData.relProj`, underlying the projective-bundle construction.
- `WeilConjectures.Blowup.AdmissibleBlowup`: `AlgebraicGeometry.IsAdmissible`, its actual
  finite-type ideal and blowup; `WeilConjectures.Compactification.StrictTransform`:
  `AlgebraicGeometry.strictTransformι`, the image of the open locus.

I added the last two existing nodes (`def-nagata-admissible-blowup` and
`lemma-nagata-strict-transform-closure-characterization`) to `stmt_deps`, since the Lean
statement now uses their recorded interfaces directly. Both were already proof
prerequisites, both have published declarations, and neither is restated. There are no
new nodes and no dependency repairs. All published proof-dependency modules are imported
non-publicly when not already imported publicly for the statement; the original
mathematical proof and proof dependencies are retained.

Edge cases checked: H_eta may be empty, in which case its kernel in C is the unit ideal,
H is empty, and the two marking transforms are empty. No nonemptiness assumption is
made on H or H_eta. The marking dimension condition has precisely the requested nonempty
premise. The curve is nonempty by irreducibility and dimension one, and its conclusion
requires all geometric fibres nonempty, as the node's proof establishes using properness.
An integral base excludes the empty base. U may be the whole base and the centre the unit
ideal, allowing the identity blowup. S may have dimension zero. No geometric integrality
of C_eta is assumed; after an algebraically closed extension its different components
are allowed, and only their dimension is prescribed. Every scheme and test field is in
universe u, with the scheme category explicitly fixed in geometric-fibre pullbacks; no
independent smaller test-field universe makes the conclusion vacuous. No regularity,
normality, algebraic closedness, field-characteristic restriction, or smoothness of the
special fibres was added.

Searches made before writing (all returned types/docstrings were inspected):

- `msearch.py`, leanfinder: "After a blowup of an integral Noetherian base the strict
  transforms of a projective generic curve and its horizontal finite etale marking are
  flat and finitely presented". Eight hits: flat morphisms, etale/smooth base-change,
  universally open flat lfp maps, and smooth maps being lfp; none gives this theorem.
- `msearch.py`, loogle: `"blowup"`. Zero hits.
- `msearch.py`, grep: `strictTransform|strict_transform|flatification|flattening`.
  Seven hits concerning convex combinations, matrix blocks and enumerative composition;
  no flatification theorem.
- `msearch.py`, leansearch: "A projective curve and a horizontal finite etale marking
  become flat and finitely presented after a blowup of the integral Noetherian base".
  Eight hits concerning flat modules, smooth-implies-lfp, lfp base change, flat restriction
  and stalk maps; none matches the existence statement.
- `rg` in upstream `WeilConjectures` for the item id returned no occurrence. Searches for
  strict transforms, schematic closure, flatification, blowup, H-projectivity, projective
  bundles, excellence and birational maps identified the reusable APIs cited above.
- `rg` in `lean/Sheaf` for the same notions identified the generic-flatness, flattening,
  dense-generic-fibre dimension and projective-bundle dependencies; none states this
  simultaneous curve-and-marking result. The proposed declaration name is absent from
  `dag/lean_names_upstream.json`, upstream sources and the side library.

Validation: `scompile.py Q117 lem-trf-flatification-horizontal-curve-pair` compiled the
sandbox file and its library-path form cleanly, with no errors or warnings. The initial
geometric-pullback category-inference errors were repaired by explicitly specifying
`(C := Scheme.{u})`. There is exactly one `sorry`, belonging to the named theorem. No
statement dispute or source correction was necessary.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
