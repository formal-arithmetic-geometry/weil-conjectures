## Worker report

The module `Sheaf.AlgebraicGeometry.StableCurveFramedTraitSmoothing` states
`AlgebraicGeometry.stable_curve_framed_trait_smoothing`, with one `sorry` and the
node's eight-step natural-language proof in its docstring. Its three construction
helpers are the specified trait over k, its residue point, and its Laurent-series
generic point. They use real coefficient/inclusion homomorphisms and no choices or
postponed data. No node statement or accepted proof split was corrected.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| g >= 2 | `C.genus_at_least_two : 2 ≤ g`, already part of the recorded stable-family structure; no genus is dropped |
| Unpointed stable genus-g curve C/k | `C : StablePointedModuli (Spec (.of k)) g 0`, with `c : Over.mk (𝟙 (Spec (.of k))) ≅ C.base` rigidifying its base to Spec k |
| The actual input curve over k | `pullback C.projection c.hom.left`; since c is an isomorphism, this is canonically C itself, not a restriction of the permitted input curves |
| r = 19(g-1), projective space P^(r-1) | The dependency's `TenCanonicalHilbert.Coordinates g`, `standard g`, and rank field of `Series`; for g >= 2 its coordinate cardinality is exactly r |
| Prescribed projective frame tau | `tau : TenCanonicalHilbert.Frame (P.series C) c.hom.left`, an isomorphism of quotient projective bundles in the slice category, not a chosen vector-space basis |
| R=k[[t]], S=Spec R with coefficient inclusion | `StableCurveFramedTrait.base k`, built from `PowerSeries k` and `PowerSeries.C` |
| Special map induced by R -> k | `StableCurveFramedTrait.special k`, using `PowerSeries.constantCoeff`; its slice commutation uses the actual identity `constantCoeff.comp C = RingHom.id k` |
| K=k((t))=R[1/t] | `StableCurveFramedTrait.generic k`, using the canonical `algebraMap (PowerSeries k) (LaurentSeries k)`; Mathlib supplies the localization-at-X structure, as used by the smoothing dependency |
| Stable unpointed genus-g family over S | Existential `X : StablePointedModuli (Spec (.of k)) g 0` and `a : base k ≅ X.base`; the actual family is `X.pullback (base k) a.hom`, with projection `pullback.snd X.projection a.hom.left` |
| Projective and flat | `IsHProjective` and `Flat` on that actual projection |
| Finitely presented | `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` on that projection, spelling out the global finite-presentation convention |
| Special-fibre isomorphism | `e : pullback (pullback.snd X.projection a.hom.left) (special k).left ≅ pullback C.projection c.hom.left`; the first equality says e is over Spec k |
| Lifted projective frame | `phi : TenCanonicalHilbert.Frame (P.series X) a.hom.left` |
| Frame restricts to exactly tau under e | The second equality compares `pullback.fst ... ≫ baseEmbedding ... ≫ phi.hom.left` with `e.hom ≫ baseEmbedding ... ≫ tau.hom.left ≫ ProjectiveSpace.map ... (special k).left` |
| Generic fibre is smooth | `Smooth (pullback.snd (pullback.snd X.projection a.hom.left) (generic k))` |
| Closed relative complete ten-canonical embedding | The actual `baseEmbedding (P.series X) a.hom.left ≫ phi.hom.left`. `Series` includes the true tenth-power pushforward, normalized evaluation counit, quotient classification, surjectivity, closed immersion, rank and arbitrary base change; `phi` supplies the standard projective coordinates |
| Map alpha:S -> J given by that embedding | Existential `alpha : base k ⟶ P.J`, with `P.hilbert.Classifies P.inclusion (P.series X) a.hom phi alpha` |
| Special point is the prescribed framed curve | Existential `beta` with `Classifies` for `(C,c,tau)` and the literal equality `special k ≫ alpha = beta` |
| Generic embedded degree 20(g-1) | `Scheme.Hom.degree` of the actual generic projection, with the hyperplane module pulled back along that same framed embedding, equals `20 * ((g : ℤ) - 1)` |
| Generic genus g | `.genus = g` for the same smooth generic projection, using the existing differential-form genus, equal to arithmetic genus for these smooth proper connected curves |

The base isomorphisms c and a are an explicit presentation of membership in a fibre
of the recorded moduli category. They impose no extra geometric restriction: every
family on the specified base has such a presentation using the identity. Keeping
them as isomorphisms avoids forcing an equality between canonically isomorphic
scheme presentations. Pullback preserves stability and the geometric genus by the
recorded `StablePointedModuli.pullback_properties` and `pullback` definitions.

The frame restriction equation is stated on the complete embeddings, making its
transport through the chosen special-fibre isomorphism explicit. This is equivalent
to equality of the restricted projective frames: the complete ten-canonical curve
is nondegenerate, and the full section space determines its ambient projective
coordinates. This includes scalar representatives of the same projective frame.
It does not require a lift of tau to a vector-space basis. `Classifies` additionally
requires the unique isomorphism to the actual Hilbert subscheme, with both the
embedding and structural maps agreeing; alpha and beta are not arbitrary maps.

The parameter `P : TenCanonicalHilbert.Presentation k g` is the already recorded
Hilbert parameter, not an extra existence assumption: the dependency theorem
`ten_canonical_hilbert_parameter` supplies it for every allowed genus. The statement
works for any such presentation and retains its precise complete-series conventions.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, used on the generic projection.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`; the ring here is concretely the prescribed power-series ring, rather than a variable DVR. The module imports this recorded convention.
- `Sheaf.AlgebraicGeometry.StablePointedCurve`: `AlgebraicGeometry.IsStablePointedCurve`, used through the `stable` field of the recorded moduli objects; its full nodal/reduced/pure-dimension and component-stability definition was read.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `StablePointedModuli`, `StablePointedModuli.pullback_properties`, `StablePointedModuli.pullback`. The genus field is geometric arithmetic genus, and r=0 retains the unpointed case.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; `Mathlib.Algebra.Field.Defs`: `Field`. No separate algebraic closure is needed when k itself is algebraically closed.
- `Mathlib.RingTheory.MvPowerSeries.Basic` and `Mathlib.RingTheory.PowerSeries.Basic`: `MvPowerSeries`, its one-variable specialization `PowerSeries`, `PowerSeries.C`, `PowerSeries.constantCoeff`.
- `Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter`: `ten_canonical_hilbert_parameter`, `TenCanonicalHilbert.Presentation`, `Series`, `Frame`, `baseEmbedding`, `standard`, `Coordinates`, `Hilbert.Classifies`; full signatures and docstrings read.
- Added existing node `def-sc-hilbert-degree`: `WeilConjectures.AlgebraicGeometry.Modules.Ample`, `AlgebraicGeometry.Scheme.Hom.degree`.
- Added existing node `def-sc-genus`: `WeilConjectures.AlgebraicGeometry.Curve`, `AlgebraicGeometry.Scheme.Hom.genus`.

The last two additions only name the existing numerical conventions used in the
node's final clause. They add no new notions, modules or mathematical assumptions.
All original statement dependencies are retained.

Proof-dependency modules imported privately, using the read recorded declarations:

| Module | Declaration |
| --- | --- |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` | `SheafOfModules.IsFiniteLocallyFreeOfRank` |
| `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper` | `AlgebraicGeometry.hProjective_properness` |
| `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange` | `AlgebraicGeometry.fibre_dimension_after_base_change` |
| `Sheaf.AlgebraicGeometry.GorensteinCurveRelativeDualizing` | `AlgebraicGeometry.exists_nodalRelativeDualizingSystem` |
| `Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothing` | `AlgebraicGeometry.isolated_lci_curve_smoothing` |
| `Sheaf.AlgebraicGeometry.NodalCurveLCICriterion` | `AlgebraicGeometry.nodal_curve_lci_criterion` |
| `Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular` | `AlgebraicGeometry.nodal_family_fitting_singular` |
| `Sheaf.TraceFormula.ProjectiveBundleProper` | `AlgebraicGeometry.projectiveBundle_proper` |
| `Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous` | `AlgebraicGeometry.isOpen_setOf_topologicalKrullDim_fiber_le` |
| `WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldDiscrete` | `AlgebraicGeometry.discreteTopology_of_unramified_over_field` |

The three proof dependencies `lem-sfb-projective-frames-pgl`,
`lem-sfb-stable-and-smooth-family-open-loci`, and
`lem-sfb-stable-curve-pluricanonical-linear-series` have no recorded Lean modules in
the current read clone, so there is no module to import. Their places in the proof
are retained in the docstring. No statement prerequisite is missing or replaced.

Edge cases checked before writing: g=2 gives r=19 and degree 20, so projective frames
are in positive projective dimension; all characteristics, including 2, are allowed;
a smooth input curve is allowed (empty singular set); reducible stable curves and
self-nodes are allowed by the reused stability predicate; zero markings are Fin 0;
the special frame is a projective automorphism class, including arbitrary scalar
representatives, not just an ordered linear basis. The stable curve is nonempty by
the recorded stability convention, so empty curves are not silently admitted.
All rings, curves, schemes, geometric fields and coefficient maps use the explicit
universe u; no test-field universe is independently lowered and no implicits are
auto-bound. Degree uses an integer cast before subtracting 1. Both field-base and
trait-base isomorphisms allow arbitrary isomorphic presentations.

Source checks: read examples-defos.tex at lemma-smoothing-proper-curve-isolated-lci
(Tag 0E7Y), and moduli-curves.tex at lemma-stable-curves and
lemma-stable-one-piece-per-genus (0E76, 0E78). They give precisely the smoothing and
stable-genus openness inputs. The node labels its framing argument as agent
synthesis; the report does not claim to have read the locally WANTED Morrison PDF.
No statement fault or STATEMENT-DISPUTED flag was found.

Searches for existing statements (2026-10-24):

- `msearch.py ... leanfinder "A stable curve over an algebraically closed field admits a smoothing over the power series ring with a prescribed ten canonical projective frame"`: eight hits, only smooth-morphism/standard-smooth/elliptic declarations; no stable framed smoothing theorem.
- `msearch.py ... leansearch "A stable curve admits a smoothing over the formal power series ring"`: eight hits, general formal smoothness and smooth loci; no match.
- `msearch.py ... loogle "PowerSeries.constantCoeff, LaurentSeries, AlgebraicGeometry.IsSmooth"`: zero hits; the service does not know the old IsSmooth spelling in that query. Corrected focused search `loogle "PowerSeries.constantCoeff"` returned the canonical residue map and twelve related declarations, including `constantCoeff_comp_C`, which the construction uses.
- `msearch.py ... grep "framed.*smoothing|smoothing.*frame|stable.*smoothing" AlgebraicGeometry`: zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the smoothing/frame names: no existing theorem stating this item. The existing isolated-lci smoothing has no stable-family or prescribed-frame conclusion. The ten-canonical parameter defines the vocabulary but makes no smoothing assertion. Upstream `grep -rn` for this exact node id gives no declaration. The full declaration name and helper namespace are absent upstream and in Sheaf.
- `rg` in `dag/lean_names_upstream.json` for the item id: no match. Read the numerical definitions and their existing DAG records instead of adding duplicates.

Validation: `scompile.py Q159 lem-sfb-stable-curve-framed-trait-smoothing <module>`
compiled the sandbox probe and the actual library module cleanly, respectively in
3.6 and 4.8 seconds, with no errors or warnings. The only theorem body is `by sorry`.
All definition data is explicit. The residue-map proof was corrected to rewrite
ring-hom composition explicitly before the successful compile.

## Second reading by Q159

The worker reread the node and the final compiled signature clause by clause, using
the correspondence table above. This is a worker self-check; the dispatcher forbids
starting another agent, and the maintainer supplies the independent review. The
reread checked particularly that e is over k, that the restriction equation uses e
rather than an unrelated curve isomorphism, that both Hilbert maps classify the
same complete embeddings and specialize literally, and that degree is computed
from the hyperplane module of that embedding. It also checked that g >= 2 is
already an explicit field of C and that the actual trait family inherits stability
and genus through the recorded pullback construction. No mismatch requiring a node
statement correction was found. No new nodes or dependency repairs are delivered.
