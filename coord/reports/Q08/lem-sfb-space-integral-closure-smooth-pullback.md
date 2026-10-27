## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.integralClosure_smooth_pullback`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceIntegralClosureSmoothPullback`. The source
is Stacks Tag 082E, read in `spaces-more-morphisms.tex`, label
`lemma-integral-closure-smooth-pullback`. It identifies the two subalgebras through
the tensor of the actual inclusion. No statement correction is needed.

Hypotheses and clauses:

- A scheme S and algebraic spaces X,Y over S: `{S : Scheme.{u}} {X Y : AlgebraicSpace S}`.
  Morphisms are the existing natural transformations: `(g : Y ⟶ X)`.
- Smoothness means precisely the node's compatible-chart test. `hg` quantifies over
  `U : Y.EtaleSite`, `V : X.EtaleSite` and every map of their schemes over S, with
  `yoneda.map a ≫ V.obj.hom = U.obj.hom ≫ g.hom.hom`; its conclusion is `Smooth a.left`.
  This does not assume that every Y-chart maps to a single X-chart.
- Universes: explicit `universe u`; schemes and rings retain universe u, full small
  etale site objects have universe u+1 and their arrows universe u. No universe equality,
  coefficient lift or smallness restriction is added.
- A commutative O_X-algebra B on the small etale site: `B : X.CommAlgebraSheaf`, the
  existing under category of the commutative structure sheaf in commutative ring sheaves.
  `hB : B.toModule.IsQuasicoherent` uses the existing local-presentation predicate.
- `C : Subobject B` is IC_X(B). `hC` is verbatim the characterization from the recorded
  Tag 0820 theorem: its underlying module is quasi-coherent and, on each affine etale
  V, the image of its inclusion consists exactly of elements satisfying a monic equation
  over the structural image of O_X(V). `RingHom.IsIntegralElem` is precisely this test;
  it does not require an injective structural map. The existing existence/uniqueness
  theorem makes C and hC a representation of that unique closure, not extra conditions
  on B or X.
- `P : AlgebraTensorPullbackModel g` supplies the algebra structure on the existing
  module tensor pullback. The new node proves existence and normalized uniqueness;
  the theorem works for EVERY such model, including its canonical selected model.
- `D : Subobject (P.functor.obj B)` and `hD` use the identical Tag 0820 characterization
  for IC_Y(g*B). Existence follows from that recorded theorem and preservation of
  quasi-coherence under module pullback, transported through P.moduleIso. It is not
  a new mathematical assumption about g or B.
- `∃! e : P.functor.obj C ≅ D` gives an isomorphism of algebra sheaves, not only modules.
  `e.hom ≫ Subobject.arrow D = P.functor.map (Subobject.arrow C)` says the map is exactly
  the one induced by pulling back the inclusion. Since the right hand side then factors
  as an isomorphism followed by a mono, it also asserts monicity of the pulled inclusion
  and equality as embedded subalgebras, with no image information forgotten.
- The uniqueness in `∃!` retains the compatibility clause of the node. After algebra
  isomorphisms, identity tensor multiplication, or the normalized tensor associator,
  the transported comparisons have the same composite with the ambient inclusion;
  uniqueness makes them equal. Thus the Lean characterization includes the canonical
  comparison rather than a bare isomorphism type. Identity and composite pullbacks are
  included by the unrestricted g and P binders. The docstring spells out the tensor
  normalization and resulting argument for each compatibility.
- There is no finite-type, reducedness, injectivity, Noetherian or nonemptiness binder.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`, `etaleForget`,
  `structureSheaf`, `Modules`; the compatible triangles use the actual site object data.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `def-weil-size-convention` has no definiendum; explicit universes implement it.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  `SheafOfModules.IsQuasicoherent` from Mathlib's local-presentation definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIntegralClosure`:
  `existsUnique_quasiCoherent_integralClosure`; its complete signature and proof
  docstring were read. Its C predicate is copied literally in hC and hD.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleChart`,
  `moduleTensorPullback`, `moduleTensorSection` and the normalized chart-limit adjunction.
- The new definition uses the already landed
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf.algebraModuleFunctor` and
  `AlgebraicSpaceQuasiCoherentAlgebra`'s `CommAlgebraSheaf` and `toModule`.

The already stated proof dependencies are imported privately: module pullback
quasi-coherence; fibre products and etale covers; normalized chart tensor realization;
affine chart calculus; scheme Zariski/etale equivalence; upstream affine pullback sections;
and Mathlib's `TensorProduct.toIntegralClosure_bijective_of_smooth`. All statement imports
are public, and there are no file-local definitions, notation, instances or unbound variables.

Edge cases checked: empty spaces and empty charts are allowed; the zero algebra and
nonfaithful structural maps use the same monic-equation test; arbitrary nonreduced and
non-Noetherian rings are allowed by the Mathlib smooth base-change theorem; B need not
be finitely generated. Identity maps are included. Smoothness is only chartwise, without
replacing the space by a scheme. Arbitrary normalized choices of pullback are included,
so no equality of independently chosen functors is assumed. Definitions contain real data;
the two named theorems alone use `sorry` and each has a full source/proof docstring.

Searches (performed with the prescribed wrapper): LeanFinder for integral closure of a
quasi-coherent algebra on an algebraic space commuting with smooth pullback returned
scheme normalization, not this statement. Loogle `"integralClosure", "Smooth"` returned
`TensorProduct.toIntegralClosure_bijective_of_smooth`; its actual signature and the
canonical `toIntegralClosure` map were read. Mathlib grep in RingTheory/Smooth found
only the ring-level result. LeanSearch for the sheaf statement returned ordinary ring
integral closure definitions. Source grep for the exact item id found no declaration.
Mathlib, WeilConjectures and Sheaf searches for algebra-space commutative-algebra
pullback found no normalized algebra functor. The scheme-Zariski
`AlgebraTensorPullbackComparison` was inspected and does not apply to algebraic spaces.
The new node includes the search wrapper's raw timestamped answer records and the
DAG/source grep results. `tools/blueprint_refs.py search 'algebra tensor pullback'`
returned zero matches. Definition-node title searches found only derived/module tensor
pullback, graded algebra and Rees maps, not this notion.

Validation: both files compiled individually, in dependency order, through scompile.py,
as sandbox modules and as their library modules, against the published live build.
No errors or non-sorry warnings were reported.

## New nodes

`def-sfb-space-algebra-tensor-pullback` defines the missing lift of module tensor pullback
to commutative algebra sheaves, with its normalized universal-property interface. Its
model consists of an algebra functor and a natural isomorphism to the ALREADY EXISTING
module pullback, with unit and multiplication specified on those same local tensors.
It also states existence and uniqueness up to the unique comparison preserving the
underlying-module identification; the selected model is chosen through this uniqueness
property, not a mere arbitrary existence witness. This is the algebra pullback used in
Stacks 082E, constructed by inverse image and tensor extension of scalars (Modules on
Sites, 03D7 and 03D8). All data of the definitions are real; the construction theorem has
its proof postponed as a named statement with a complete construction/uniqueness proof
in the docstring. The recorded Mathlib, DAG and source searches found no existing
algebraic-space algebra tensor-pullback notion. The item gains only this statement
dependency and its Lean record; all other original fields remain unchanged.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
