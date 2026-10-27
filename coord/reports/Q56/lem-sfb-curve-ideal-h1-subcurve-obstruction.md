## Worker report

The new module `Sheaf.AlgebraicGeometry.CurveIdealH1SubcurveObstruction` states
`AlgebraicGeometry.exists_subcurve_degree_le_of_ideal_h1_nonzero`, with a single
`sorry` proof. It introduces no definitions, auxiliary assumptions, or new nodes.
The item JSON changes only in `lean`; its signature is copied verbatim from the module.

Source read: `literature/stacks-project/curves.tex`, Tag 0E3E,
`lemma-vanishing-on-gorenstein`, statement and complete proof (lines 5462--5535).
The node agrees with that source, including the passage to a connected component
before the final Euler calculation. Its seven proof steps are recorded in the theorem
docstring with the named DAG inputs. There is no statement dispute or correction.

Hypothesis and conclusion correspondence:

- The arbitrary field is `(k : Type u) [Field k]`. There is no algebraic-closure or
  characteristic hypothesis.
- The scheme over k is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`; the fixed structure
  morphism is `X ↘ Spec (.of k)`.
- Properness is `[IsProper (X ↘ Spec (.of k))]`; reducedness is `[IsReduced X]`;
  connectedness is `[ConnectedSpace X]`. The latter includes nonemptiness, as the
  connected-scheme dependency specifies.
- Dimension one is `hdim : topologicalKrullDim X = 1`. Pure dimension, Noetherianity,
  and coherence are consequences used in the proof, not extra hypotheses.
- The invertible module is `(L : X.Modules) [L.IsInvertible]`.
- A closed subscheme is presented by `(Z : Scheme.{u}) (i : Z ⟶ X)
  [IsClosedImmersion i]`. Its ideal is exactly `i.ker.toModules`.
- Zero-dimensional, possibly empty, is `hZ : topologicalKrullDim Z ≤ 0`:
  the dimension convention of `def-kun-topological-krull-dimension` gives the empty
  scheme dimension bottom. Equality to zero would incorrectly exclude empty Z.
- The tensor is `(i.ker.toModules ⊗ L : X.Modules)`. Nonzero first module cohomology
  is `hH : ¬ Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj ...)`.
  For an additive group this is exactly nonvanishing. This uses the recorded
  right-derived module cohomology, rather than replacing it by abelian-sheaf Ext.
- The subcurve is `∃ (B : Scheme.{u}) (b : B ⟶ X), ...`. Its closedness is
  `IsClosedImmersion b`, its reducedness `IsReduced B`, its connectedness and
  nonemptiness together `ConnectedSpace B`, and its dimension `topologicalKrullDim B = 1`.
- Restriction of L is `((Scheme.Modules.tensorPullback b).obj L)`, the dependency's
  explicit sheafified tensor pullback.
- The left side is the recorded `Scheme.Modules.degree` of that pullback, with the
  actual induced `B.Over (Spec (.of k))` structure `⟨b ≫ X ↘ Spec (.of k)⟩`.
- The first term on the right is `-2 * Scheme.Modules.eulerChar ...` of
  `SheafOfModules.unit B.ringCatSheaf`, with the same induced structure map.
- The intersection is `pullback i b`, literally Z times_X B, with its actual
  scheme structure. Its global sections are `Γ(pullback i b, ⊤)`.
- The final term is `Module.finrank k` of that section ring, cast to the integer
  target of degree/Euler characteristic. Its module instance is specified with
  `Module.compHom` along
  `((Scheme.ΓSpecIso (.of k)).inv ≫
    (pullback.fst i b ≫ i ≫ X ↘ Spec (.of k)).appTop).hom`.
  This is the defining formula for `Scheme.globalSectionsRingHom` with the induced
  intersection structure morphism. Thus there is no arbitrary scalar action,
  choice of k-structure, rational-point assumption, or geometric-point count.
  The pullback relation identifies the alternative route through B.
- The relation is exactly `≤`, with integer arithmetic: degree is at most minus
  twice chi plus the k-dimension of intersection sections. No stronger conclusion
  such as B being integral or smooth is imposed.

Dependency declarations read and used:

| Node | Module and declarations |
| --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs: `Field` |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper: `AlgebraicGeometry.IsProper` |
| def-pc-reduced-scheme | Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsReduced` |
| def-weil-connected-scheme | Mathlib.Topology.Connected.Basic: `ConnectedSpace`, including `toNonempty` |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension: `topologicalKrullDim` |
| def-sc-invertible-module | WeilConjectures.AlgebraicGeometry.Modules.Invertible: `AlgebraicGeometry.Scheme.Modules.IsInvertible` and the existing scheme-module tensor instance |
| def-sbc-closed-immersion-ideal-sheaf | Mathlib.AlgebraicGeometry.IdealSheaf.Basic: `AlgebraicGeometry.Scheme.Hom.ker`; WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module: `Scheme.IdealSheafData.toModules` |
| def-sc-ringed-space-module-cohomology | WeilConjectures.Topology.RingedSpaceModuleCohomology: `AlgebraicGeometry.RingedSpace.moduleCohomology` |
| def-pur-sheaf-tensor-product | Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: `SheafOfModules.cochainModulesMonoidal`, retaining the existing localization tensor by public imports |
| def-pc-module-pullback | Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction, publicly importing WeilConjectures.AlgebraicGeometry.TensorPullback: `Scheme.Modules.tensorPullback` |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.fst`; Mathlib.AlgebraicGeometry.Pullbacks provides scheme pullbacks |
| def-pc-degree-line-bundle | WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar: `Scheme.Modules.degree` |
| def-pc-euler-characteristic | WeilConjectures.AlgebraicGeometry.Cohomology.Defs: `Scheme.Modules.eulerChar`, also `Scheme.globalSectionsRingHom` for the scalar-action formula |

The recorded public dependency modules are imported. The already stated proof inputs
are plain imports: CoherentFiniteTypeLocallyNoetherian, ReducedCurveDualizingModule,
CoherentKernelCokernelSum, EulerCharZeroDimSupport, and Cohomology.LongExact.
The Mathlib properness-of-closed-immersion/composition tools are available through
Morphisms.Proper. Two proof-only nodes currently have neither a Lean record nor an
audit declaration: `lem-trf-proper-field-invertible-coherent` and
`lem-sfb-closed-subcurve-dualizing-adjunction`. They do not occur in the theorem's
type, so no replacement declaration or invented module is needed. Their statements
remain named explicitly in the proof docstring for stage 3. No import is omitted
for an import cycle.

Searches actually run through `msearch.py Q56 <item>`:

- LeanSearch: “Nonzero first cohomology of the ideal of a finite subscheme tensor a
  line bundle on a proper reduced connected curve implies a connected subcurve of
  small degree”. Eight hits, about cotangent H1, ideal supports and group cohomology;
  none states the obstruction.
- LeanFinder: “Nonzero first cohomology ideal tensor line bundle proper reduced curve
  subcurve degree Euler characteristic bound”. Eight hits, concerning Weierstrass
  division-polynomial degrees and other algebraic degrees; none matches.
- Loogle: `"AlgebraicGeometry", "cohomology", "degree"`: zero hits.
- Mathlib grep: `subcurve|vanishing.on.gorenstein|ideal.*[Hh]1` in AlgebraicGeometry:
  zero hits.
- Source/project `rg`: `subcurve|vanishing.on.gorenstein|lem-sfb-curve-ideal-h1-subcurve-obstruction|exists.*degree.*eulerChar`
  in `lean/WeilConjectures` and `lean/Sheaf`. Existing matches describe open subcurves,
  nodal subcurve geometry, and the consumer NodalNumericalVeryAmple's proof plan;
  none gives this theorem. The proof consumer is not an existing declaration of this
  result. A further declaration-name search `exists_curve_ideal|h1_subcurve_obstruction|exists.*subcurve.*degree`
  in both source roots and `dag/lean_names_upstream.json` found no collision.

Edge cases checked mathematically before finalizing the signature:

- Empty Z is allowed by `≤ 0`; its ideal is the unit ideal. The intersection can
  also be empty when Z is nonempty; its zero section ring has k-finrank zero.
- On P1 over k with L = O(d) and a finite subscheme of length m, the H1 condition
  becomes d - m ≤ -2. Taking B = P1 gives exactly d ≤ -2 + m.
- For P1 over a finite field extension k'/k viewed as a k-curve, all Euler
  characteristics, degrees and lengths scale by [k':k]. There is no hidden
  H0(O_B) = k or geometric-connectedness assumption.
- Nonreduced zero-dimensional Z is allowed; there is no reducedness or Cartier
  condition on Z. The ideal tensor, not a divisor line bundle, occurs in H1.
- Reducible reduced curves, including nodal intersections, are allowed; the
  conclusion requires connectedness, not irreducibility, and retains intersection
  nilpotents in the pullback scheme and its section ring.
- Non-Gorenstein reduced curves and every characteristic are allowed. Dualizing
  modules are proof tools; no invertibility of omega or smoothness is assumed.
- Empty X or B is excluded exactly by connectedness (and dimension one). All
  schemes and the field lie in a common arbitrary universe u, matching the
  recorded degree and module-cohomology interfaces; no small test universe occurs.

Validation: `scompile.py Q56 lem-sfb-curve-ideal-h1-subcurve-obstruction
<module path>` compiled both the sandbox probe and library module cleanly, each in
1.8 seconds. Both implicit-variable options are disabled, every Lean line is at
most 100 characters, and the only proof in the delivered file is `by sorry`.

## Second reading by Q56

I made a separate source-and-signature reading after the successful compile,
with the node and Stacks 0E3E open. This is a second pass by the assigned worker;
the dispatcher's instruction prohibits starting a separate reader agent. The
maintainer's independent review remains separate from this report.

The quantifiers give an arbitrary field, a proper reduced connected dimension-one
scheme, an invertible module, and any closed immersion of dimension at most zero.
The latter is the node's explicitly permitted empty-or-zero-dimensional Z, not a
restriction to nonempty finite subschemes. The cohomology is the recorded right
derived functor on O_X-modules applied to the canonical ideal tensor L. The
existential B has the exact closed/reduced/connected/dimension-one clauses;
ConnectedSpace supplies its nonemptiness. Both degree and chi use the composite
map b followed by the structure map of X. The last summand is the integer cast of
the dimension of sections on the actual pullback Z times_X B, along its induced
k-action. Thus scheme-theoretic multiplicities and nonrational residue fields are
retained. There are no extra finite-dimensionality, purity, smoothness,
Gorensteinness, Cartier, or algebraic-closure hypotheses. The seven proof paragraphs
match the node's sequence of reductions, including I/JI versus (I+J)/J and the
connected-component restriction before the Euler calculation. No mismatch was
found and no signature change was needed on this pass.
