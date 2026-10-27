## Worker report

The module `Sheaf.AlgebraicGeometry.ProperGenericMapBigOpen` states
`AlgebraicGeometry.proper_generic_map_big_open`. Its sole theorem has proof `sorry`.
No definitions, new nodes, dependency repairs, or statement changes were needed.
The accepted DAG statement and proof are unchanged. The theorem docstring carries
all seven proof steps, including the local-ring classification used for the
valuative square, relative separatedness for comparison and gluing, and the
principal ideal height argument for fibrewise density.

Source checked: Bosch--Lutkebohmert--Raynaud, Neron Models, 1.2 Proposition 8,
proof on printed p.15 (PDF p.21), before Weil extension; 1.2 Lemma 5 for local
spreading. The primary scan named by the node was opened online at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The preliminary properness argument is independent of the group structure;
the subsequent global extension is the step that uses it. Also read the local
Stacks sources: morphisms.tex, lemma-morphism-defined-local-ring (0BX6),
lemma-extend-across (0BX7), and descent.tex, lemma-normal-local-smooth (034F).

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| D a commutative Noetherian integrally closed domain | `D : Type u`, `[CommRing D]`, `[IsDomain D]`, `[IsNoetherianRing D]`, `[IsIntegrallyClosed D]` |
| Krull dimension one | `hD : ringKrullDim D = 1` |
| E its fraction field | `E : Type u`, `[Field E]`, `[Algebra D E]`, `[IsFractionRing D E]` |
| T a nonempty open subscheme of Spec D | `T : (Spec (.of D)).Opens`, `hT : Nonempty T`; its scheme is `T.toScheme`, inclusion `T.ι` |
| Canonical generic inclusion Spec E into T | `η : Spec (.of E) ⟶ T.toScheme`, characterized by `hη : η ≫ T.ι = Spec.map (CommRingCat.ofHom (algebraMap D E))` |
| X and Y schemes over T | `X Y : Over T.toScheme`, with structure morphisms `X.hom`, `Y.hom` |
| X affine and smooth over T | `[IsAffine X.left]`, `[Smooth X.hom]` |
| Y proper over T | `[IsProper Y.hom]` |
| Generic fibres X_E, Y_E | `(Over.pullback η).obj X`, `(Over.pullback η).obj Y`; underlying schemes are the chosen fibre products |
| Every E-morphism f_E | `fE : (Over.pullback η).obj X ⟶ (Over.pullback η).obj Y`; the Over morphism includes compatibility with Spec E |
| There exists an open V in X | `∃ V : X.left.Opens`; the open subscheme is `V.toScheme`, with inclusion `V.ι` |
| A T-morphism v from V to Y | `v : Over.mk (V.ι ≫ X.hom) ⟶ Y` |
| V_E equals all of X_E | `IsIso (((Over.pullback η).map (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X)).left)` |
| v_E equals f_E | `(Over.pullback η).map v = (Over.pullback η).map (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) ≫ fE` |
| Every x with local dimension at most one lies in V | `∀ x : X.left, ringKrullDim (X.left.presheaf.stalk x) ≤ 1 → x ∈ V` |
| V_t dense in X_t for every t | `∀ t : T.toScheme, Dense ((X.hom.fiberι t) ⁻¹' (V : Set X.left))` |
| No group structure or smoothness on Y | No such binders occur; Y is an arbitrary object of Over T with proper structure map |

The data η and hη only name the canonical inclusion implicit in the node. They
do not restrict the base: the image of Spec E in Spec D is the generic point of
the integral spectrum, every nonempty open contains it, and the universal property
of the open immersion T.ι gives a unique factorization. Thus all such D, E and T
admit exactly this map. It is not an arbitrary map from an unspecified generic point.
The relative fibre products are the prescribed ones over T, not over Spec D.

The displayed isomorphism is the base change of the actual open inclusion V.ι.
It therefore asserts precisely that the generic open subscheme is the entire
X_E, without choosing a noncanonical identification of schemes. The equality
of maps uses this same inclusion and hence is exactly restriction compatibility.
On each fibre the inverse image of V along `fiberι` is the underlying open of
V ×_T Spec κ(t), so the Dense clause is exactly the requested fibrewise density.
In particular it is not merely density in the total space.

Statement dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`;
  `AlgebraicGeometry.IsAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme` and `Scheme.Opens.toScheme`, `Scheme.Opens.ι`
  from `Mathlib.AlgebraicGeometry.Restrict` realize the affine and open clauses.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, on both D and the stalks.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
  Its documented scheme/morphism interface is `CategoryTheory.Over.pullback`,
  with underlying chosen pullback and the canonical induced map. The dependency's
  primary declaration `Scheme.Modules.moduleBaseChange` concerns modules and
  is not used as a replacement for scheme base change.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`; the fibre construction in
  `Mathlib.AlgebraicGeometry.Fiber` is `Scheme.Hom.fiber` and `fiberι`,
  defined using `Scheme.fromSpecResidueField`.

The statement modules are public imports; all available proof-dependency
modules are plain imports (or are already public statement imports).
`lem-sfb-smooth-normal-ascent` and `lem-sfb-normal-locally-finite-components`
have neither a Lean record nor a Mathlib match in the read DAG, so there is no
module to import for those two proof-only inputs. They are retained in the DAG
proof and in the theorem's proof plan; they are not needed to type this statement.

Edge cases checked before writing:

- Empty affine X: choose V empty; the generic inclusion is an isomorphism of
  empty schemes, map equality holds, the local-ring clause has no points, and
  every empty fibre has dense empty open. No nonemptiness on X is imposed.
- Empty fibres of a nonempty X: the Dense clause holds in the empty fibre.
- T can consist of the generic point (e.g. the generic open of a local DVR).
  No closed point or DVR stalk is required at that point; the full generic
  fibre clause settles its density. No requirement that T have dimension one
  has been inserted.
- X may be disconnected: there is no IsIntegral or irreducibility hypothesis
  on X. Its finitely many normal components are handled in the proof plan.
- Proper target not a group and not smooth: e.g. projective-space targets are
  included. A rational map with a vertical codimension-two indeterminacy need
  not extend on all of X; the conclusion only requires the specified open.
- Dimension-zero stalks are included by `≤ 1`, not only dimension-one stalks.
- All objects use an explicitly declared common universe u. There are no
  hidden auto-implicit variables; `set_option autoImplicit false` is set.

Searches made using the prescribed `msearch.py` wrapper:

1. LeanFinder: "A generic fibre morphism from a smooth affine scheme over a
   Dedekind domain to a proper scheme extends to a fibrewise dense open
   containing every point of local dimension at most one". Eight hits:
   PartialMap.dense_domain, PartialMap.exists_restrict_isOver,
   RationalMap.dense_domain, PartialMap.fromFunctionField, IsDominant,
   instIsPreimmersionFiberι, RationalMap.ofFunctionField,
   RationalMap.fromFunctionField. These supply density or rational-map
   infrastructure, not the requested extension assertion.
2. Loogle: `"RationalMap", "IsProper"`. Zero hits.
3. Mathlib grep: `extend_across|codimension.*proper|proper.*codimension|RationalMap.*IsProper`.
   One irrelevant simplicial-set codimension hit; no algebraic geometry match.
4. LeanSearch: "A map of generic fibres of schemes over a Dedekind domain
   with smooth affine source and proper target extends to a fibrewise dense
   open containing all points whose local rings have dimension at most one".
   Eight hits: PartialMap.dense_domain, PartialMap.mk,
   RationalMap.dense_domain, Scheme.Hom.denseRange,
   PartialMap.restrict_domain, Scheme.Hom.toPartialMap,
   PartialMap.Opens.isDominant_homOfLE, PartialMap.fromFunctionField_restrict.
   None gives this extension theorem.
5. `rg -n` in `lean/WeilConjectures` and `lean/Sheaf`:
   `proper_generic|proper.*big_open|fibrewise.*dense|fiberwise.*dense|generic.*codimension`.
   Hits concern etale covers, purity, or unrelated density statements; no match.
   `grep -rn lem-sfb-proper-generic-map-big-open lean/WeilConjectures`
   returned no hits. The proposed theorem name was also searched in both
   libraries and `dag/lean_names_upstream.json`; no collision was found.

No STATEMENT-DISPUTED flag or node fault was found. The theorem compiled cleanly
with `scompile.py` against the live published build (2.0 seconds for the module).
Only this sandbox was edited. The final imports also receive the prescribed
per-file compile in the delivery dry run.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
