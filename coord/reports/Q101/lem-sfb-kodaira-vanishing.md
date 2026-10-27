## Worker report

The module `Sheaf.AlgebraicGeometry.KodairaVanishing` states
`AlgebraicGeometry.kodaira_vanishing` with one `sorry`, its whole proof. It
introduces no definitions. The node statement is unchanged. Its dependency list
gains three already recorded and landed definition nodes, making the existing
relative differential sheaf, sheaf exterior power and geometric integrality
interfaces explicit. All writes are inside this item's sandbox.

Hypothesis and clause correspondence:

- The field F is `(F : Type u) [Field F]`; algebraic closedness is
  `[IsAlgClosed F]`, and characteristic zero is `[CharZero F]`.
- The F-scheme is `(Y : Scheme.{u}) (f : Y ⟶ Spec (.of F))`. The structure
  morphism is explicit rather than an additional choice of a scheme over F.
- Smoothness and pure dimension n ≥ 0 are `(n : ℕ)` and
  `[SmoothOfRelativeDimension n f]`. Over a field, the relative dimension is
  exactly the dimension of Y. This class includes smoothness; an extra Smooth
  hypothesis is unnecessary. This is the interface recorded on
  def-sbc-smooth-morphisms, not a new constant-dimension predicate.
- Projectivity is `[IsProjective f]`, the project's H-projective and
  quasi-compact convention, exactly the recorded def-pc-projective-morphism.
- Geometric integrality is `[GeometricallyIntegral f]`, Mathlib's integrality
  after every field-valued base change. It includes nonemptiness over F, so a
  separate `[IsIntegral Y]` binder would duplicate a consequence.
- The differential sheaf is `f.relativeDifferentials`, the actual sheafification
  of relative Kähler differentials. The upstream affine and restriction
  isomorphisms identify it with the glued modules Ω_(A/F) in the node.
- The canonical module is `Scheme.Modules.exteriorSheaf f.relativeDifferentials n`.
  Its sectionwise exterior-power presheaf and semilinear restriction maps are
  the existing alternating exterior construction. The degree-zero isomorphism
  `exteriorSheaf_zero_iso` identifies it with O_Y; no canonical bundle chosen
  by existence or unknown data is introduced.
- The module A is `(A : Y.Modules)`, invertibility is `[A.IsInvertible]`, and
  ampleness is `(hA : Scheme.Modules.IsAmple Y A)`. This is the absolute
  Stacks 01PS ampleness recorded on def-weil-pbc-ample-invertible-module,
  including quasi-compactness and affine section loci; it is not the similarly
  named relative ampleness predicate used by one proof dependency.
- Tensor product is the existing sheaf tensor `⊗` on `Y.Modules`, with the
  recorded independent-universe tensor interface imported publicly.
- The index and positivity are `(i : ℕ) (hi : 0 < i)`. There is no upper bound
  on i and no restriction to dimension at least one.
- `RingedSpace.moduleCohomology Y.toRingedSpace i` is by definition the i-th
  right derived functor of module-valued global sections on Zariski O_Y-modules,
  not Ext cohomology of a bare abelian sheaf. The conclusion `IsZero` is in
  ModuleCat of the global sections ring and says exactly that this module is zero.

Dependency declarations read and used:

- def-weil-field: `Field` in Mathlib.Algebra.Field.Defs.
- def-weil-algebraic-closure: `IsAlgClosed` in Mathlib.FieldTheory.IsAlgClosed.Basic;
  the record explicitly includes this predicate as the algebraically closed
  clause, so constructing a fixed AlgebraicClosure would change the objects.
- def-pc-scheme: `AlgebraicGeometry.Scheme` in Mathlib.AlgebraicGeometry.Scheme.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.SmoothOfRelativeDimension` and
  `Smooth` in Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- def-pc-projective-morphism: `AlgebraicGeometry.IsProjective` in
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective.
- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral` in
  Mathlib.AlgebraicGeometry.Properties, used by the geometric integrality class.
- def-weil-pbc-kahler-differentials: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation` in Mathlib.RingTheory.Kaehler.Basic,
  the module notion underlying the existing relative differential construction.
- def-weil-pbc-ample-invertible-module: `AlgebraicGeometry.Scheme.Modules.IsAmple`
  in WeilConjectures.AlgebraicGeometry.Ample.
- def-sc-invertible-module: `AlgebraicGeometry.Scheme.Modules.IsInvertible`
  in WeilConjectures.AlgebraicGeometry.Modules.Invertible.
- pqf-def-cohomology: `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`
  in WeilConjectures.AlgebraicGeometry.PQFCohomology, exposing the exact
  `AlgebraicGeometry.RingedSpace.moduleCohomology` used here; its definition was
  also read in WeilConjectures.Topology.RingedSpaceModuleCohomology.
- def-pur-sheaf-tensor-product: `SheafOfModules.cochainModulesMonoidal`
  in Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses.
- Added def-sc-relative-differential-sheaf:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` in
  WeilConjectures.AlgebraicGeometry.Modules.Differentials. Read its construction,
  universal derivation and affine/restriction comparison interfaces.
- Added def-sc-sheaf-exterior-power:
  `AlgebraicGeometry.Scheme.Modules.exteriorSheaf` in
  Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf. Read the real presheaf and
  sheafification construction and its degree-zero isomorphism.
- Added def-pc-geometrically-irreducible:
  `AlgebraicGeometry.GeometricallyIntegral` in
  Mathlib.AlgebraicGeometry.Geometrically.Integral. The node explicitly includes
  geometric integrality among its four predicates and its record names this class.

All proof dependencies with recorded Lean modules are imported as plain imports
unless their modules are already public statement imports. This includes
KollarSmoothDivisorInjectivity and the Serre, coherence, projective finiteness,
affine-loci and Bertini inputs. The only proof dependency without a recorded Lean
module or Mathlib match is lem-trf-proper-field-invertible-coherent; it therefore
has no import yet. It is named in the full five-step natural-language proof
in the theorem docstring. No unstated proof dependency is used as a definition.

Source verification: read Popa's author PDF
https://people.math.harvard.edu/~mpopa/271/Kodaira-posted.pdf, section 1.6 opening
paragraph (printed p.22), Theorem 1.6.1 (p.23), Theorem 1.6.6 and the final
injectivity/Serre proof (pp.26–28). The opening paragraph explicitly extends
these results from C to every algebraically closed characteristic-zero field.
The canonical bundle is defined as the top exterior power at the opening of
section 1.1 (p.1). No source-based correction is needed.

Edge cases checked before writing:

- n = 0: Spec F has differential sheaf zero; its zeroth exterior power is O_Y,
  and its positive cohomology vanishes. This case is allowed by the signature.
- i = 0: excluded exactly by `hi`; on Spec F an invertible module has nonzero
  global sections, so dropping positivity would give a false statement.
- i > n: included; the conclusion does not silently restrict the degree range.
- Empty Y: excluded by geometric integrality, matching the stated hypotheses.
  An empty Bertini zero divisor in the proof is permitted and is not confused
  with an empty ambient scheme, including when n = 0.
- P^1 and A = O(d), d > 0: the canonical tensor is O(d-2), whose H^1 vanishes.
  For A = O, H^1 of O(-2) does not vanish, confirming ampleness is essential.
- Positive characteristic is excluded exactly by CharZero; no embedding in C,
  extra rank formula, chosen canonical-bundle isomorphism, or finite-dimensional
  cohomology hypothesis is added.
- The arbitrary universe u houses both F and Y, following the project convention;
  no lower-universe quantified test schemes or fields create vacuous hypotheses.

Searches for an existing theorem and notions:

- msearch.py leanfinder, query “Kodaira vanishing positive sheaf cohomology
  canonical bundle tensor ample line bundle smooth projective variety characteristic
  zero”: eight hits (cotangent finiteness, affine limit sections and projective Ext
  vanishing), none the Kodaira theorem.
- msearch.py leansearch, query “Kodaira vanishing higher cohomology canonical sheaf
  tensor ample line bundle”: eight hits on affine sections, vanishing ideals and
  cotangent modules, none the theorem.
- msearch.py loogle, query `kodaira, AlgebraicGeometry.SmoothOfRelativeDimension,
  IsZero`: zero hits; unknown identifier kodaira.
- msearch.py grep, query `kodaira|Kodaira|exteriorSheaf` against Mathlib: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for `kodaira|Kodaira|lem-sfb-kodaira-vanishing`:
  only the source citation in KollarSmoothDivisorInjectivity, no Kodaira declaration.
- rg in both project roots for `exteriorSheaf|relativeDifferentials|GeometricallyIntegral`:
  found the precise existing constructions and the Kollár consumer, whose full
  signature and docstring were read. DAG search found the three existing definition
  nodes listed above, so no new node and no duplicate construction is needed.

There is no STATEMENT-DISPUTED issue and no statement correction or dependency repair.

## Second reading by Q101

I reopened the node and the written theorem for a separate self-review pass.
No additional worker was started, as required by the dispatcher brief; the
maintainer supplies the independent delivery review. This is a self-review,
not a claim of an independent worker reading.

The second pass checked every hypothesis against the source: Field, IsAlgClosed,
CharZero, structural morphism to Spec F, smooth pure dimension n, projectivity,
geometric integrality, invertibility and absolute ampleness all appear exactly.
The top exterior power and the sheaf tensor occur inside the actual module
cohomology functor, and the conclusion quantifies over exactly i > 0. It found
no mismatch. In particular, `IsZero` is applied to a bundled ModuleCat object,
not to a bare type, and no arbitrary sheaf is substituted for the canonical one.
The three added dependencies reuse landed definitions and alter no statement.
Direct imports of Scheme, Properties, Smooth and Field.Defs were made explicit
in this pass so the record-to-import correspondence is visible.

Validation: the prescribed scompile.py command for the delivered module exited 0.
Both sandbox and library compilation passed with no errors or unexpected warnings.
The only postponed proof is AlgebraicGeometry.kodaira_vanishing.
