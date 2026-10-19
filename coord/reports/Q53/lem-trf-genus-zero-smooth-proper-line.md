## Worker report

The module `Sheaf.TraceFormula.GenusZeroSmoothProperLine` states
`AlgebraicGeometry.genus_zero_smooth_proper_line`. Its only theorem has proof
`sorry`. The item changes only in `lean`; all dependency records remain unchanged.
There are no new definitions, auxiliary axioms, new nodes, or dependency modules.

The source read is `literature/stacks-project/curves.tex`,
`proposition-projective-line` (Tag 0C6U), especially (8) and its reduction to the
 degree-one linear system in (6). The smooth connected curve is integral, has a
regular closed point, and its residue field is k by algebraic closedness. Thus
this is the stated algebraically closed specialization of the source. The module
docstring follows all six DAG proof steps, including the coincident Q=R tangent
case and the affine-ideal argument that upgrades the surjective closed immersion.

Hypothesis and conclusion correspondence:

* The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
* The scheme over k is `(C : Scheme.{u}) [C.Over (Spec (.of k))]`. The notation
  `C ↘ Spec (.of k)` is its actual structural morphism.
* The connected curve is `[IsConnectedCurve (C ↘ Spec (.of k))]`. This existing
  class extends the recorded `IsCurve`, so it includes separatedness, local finite
  type, quasi-compactness, and dimension at most one; its additional fields give
  `ConnectedSpace C` (including nonemptiness) and dimension exactly one.
* Smoothness and properness are respectively
  `[Smooth (C ↘ Spec (.of k))]` and `[IsProper (C ↘ Spec (.of k))]`.
* The genus-zero condition is `(h : (C ↘ Spec (.of k)).genus = 0)`, using precisely
  the declaration recorded on `def-sc-genus`. Its current `main-20261015`
  blueprint_update defines genus by H^0 of relative differentials, with H^1 of
  the structure sheaf as the equivalent description. The node's displayed
  `g(C)=dim_k H^1(C,O_C)` has that meaning on the stated smooth proper connected
  curves; it is not a further independent hypothesis. I read the genus definition
  and `Scheme.genus_eq_arithmeticGenus` in the imported Riemann--Roch module.
  Accordingly the existing genus definition is reused, with no reattachment or
  duplicate definition. Its equivalence to H^1 is a theorem, not a definitional
  equality, and is not claimed as already proved by this statement delivery.
* The conclusion is `Nonempty ((Over.mk (C ↘ Spec (.of k)) :
  Over (Spec (.of k))) ≅ Over.mk (ProjectiveSpace (ULift.{u} (Fin 2))
  (Spec (.of k)) ↘ Spec (.of k)))`. An isomorphism in the slice is exactly a
  scheme isomorphism commuting with the k-structural morphisms. The target is the
  recorded base-change projective space. `ULift.{u} (Fin 2)` gives precisely two
  homogeneous coordinates in the scheme universe, hence projective one-space.
  `Nonempty` asserts existence and does not choose an arbitrary canonical model.

Dependency declarations read and used:

* `def-nagata-projective-space-base-change`: `AlgebraicGeometry.ProjectiveSpace`
  in `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`. Its definition is the
  pullback of integral Proj along the base structural map; its canonical `Over`
  map is the first projection. The full declaration and docstring were read.
* `def-sc-curves`: `AlgebraicGeometry.IsCurve`, together with its already existing
  `IsConnectedCurve` extension in `WeilConjectures.AlgebraicGeometry.Curve`.
  Both full class definitions/docstrings were read. Connectedness is the node's
  specified connected-curve notion, not an assumption of geometric integrality.
* `def-sc-genus`: `AlgebraicGeometry.Scheme.Hom.genus`, in the same Curve module.
  Its complete definition/docstring and the dependency's current blueprint update
  were read, as explained above.

All stated proof-dependency modules are imported non-publicly: smooth-curve local
rings, closed-point fields, divisor modules, their local descriptions,
Riemann--Roch, point/tangent separation, standard projective charts, and closed
immersions. `def-sc-pic0` is already supplied by the public Curve import, and
projective-space base change by the public ProjectiveSpace import. The two public
Mathlib imports provide the smoothness and algebraically closed field predicates
in the signature. No proof dependency was omitted for an import cycle.

Edge cases checked before the final statement:

* The empty scheme and Spec k have dimension bottom and zero respectively, so
  cannot satisfy the dimension-one connected-curve class. A disjoint union fails
  the connectedness field. No separate nonemptiness assumption is needed.
* All field characteristics are permitted, including characteristic two; no
  finite-field, projective, rational-point, geometrically integral, or chosen
  point hypothesis is added.
* Universes are explicit (`u`, `k : Type u`, `C : Scheme.{u}`); the lift of Fin 2
  prevents accidentally forcing the field and scheme into universe zero.
* The genus is a natural number and the actual zero value is allowed. Properness
  supplies the setting for its finite-dimensional geometric meaning.
* The isomorphism is over k, not just an isomorphism of the underlying schemes.

Searches made (UTC date 2026-10-17):

* `msearch.py leanfinder`: `smooth proper connected curve genus zero algebraically
  closed isomorphic projective line`. Eight Weierstrass-curve/model hits; none
  classifies arbitrary smooth proper genus-zero curves.
* `msearch.py leansearch`: `Every smooth proper connected genus zero curve over an
  algebraically closed field is isomorphic over the field to projective one
  space`. Eight hits about properness, smoothness, affine-space emptiness, and
  Weierstrass points; no classification theorem.
* `msearch.py loogle`: `genus, arithmeticGenus, ProjectiveSpace` returned zero
  hits (unknown identifier genus); the subsequent quoted-name query `"genus"`
  returned zero hits.
* `msearch.py grep`: `genus_zero_smooth_proper_line|arithmeticGenus|IsConnectedCurve`
  in Mathlib's AlgebraicGeometry directory returned zero hits.
* `rg` in upstream WeilConjectures and project `lean/Sheaf` for genus-zero/genus=0
  and the item id found the projective-line genus-zero theorem, whose complete
  signature/docstring I read: it is the converse statement, not this classification.
  Upstream has genus definitions and duality, not this theorem. The proposed full
  theorem name was also searched in `dag/lean_names_upstream.json`, upstream, and
  `lean/Sheaf`, with no hits. No existing exact theorem was found.

There is no STATEMENT-DISPUTED flag, no source-based statement correction, and no
unusable dependency. Validation: the final module compiled through `scompile.py`
in both sandbox and library-path modes, with no errors or warnings.

## Second reading by Q53

Author's self-check, not an independent review: I reopened the node and final
module and compared the field, algebraic-closedness, base, curve, connectedness,
smoothness, properness, and genus-zero binders with every hypothesis in the node.
The conclusion keeps the base map and the specified two-coordinate base-change
projective space. The current genus blueprint update and the equivalence to H^1
were checked explicitly, and no dependency record is changed. The named theorem
is the only postponed statement, its proof is wholly sorry, and its docstring
contains all six DAG proof steps. Independent review remains the maintainer's.
