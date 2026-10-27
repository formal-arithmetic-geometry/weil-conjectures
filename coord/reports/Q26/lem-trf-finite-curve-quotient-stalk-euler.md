## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteCurveQuotientStalkEuler` states
`AlgebraicGeometry.Scheme.Modules.finite_curve_quotient_stalk_euler`, with `sorry`.
There is no statement correction and no disputed assertion. The repository node is
copied unchanged except for its new `lean` record.

Sources read: Stacks `literature/stacks-project/varieties.tex`,
`lemma-prepare-delta-invariant` (Tag 0C1R), statement and proof, and
`lemma-chi-tensor-finite` (Tag 0AYT), statement and proof. The first supplies the
normalization quotient argument, here with the node's expressly generalized
finite modification hypothesis; the second supplies the finite-support germs,
cohomology and Euler calculation. The generalization does not assume Y reduced:
a nilpotent thickening at finitely many closed points is allowed.

The three helpers belong to the quotient already introduced in this node, rather
than introduce an independent notion. `finiteCurveQuotient f` abbreviates the
actual categorical cokernel of the existing canonical structure-sheaf morphism
`SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`.
`finiteCurveQuotientSections k f` applies the existing ringed-space global
sections functor followed by `ModuleCat.restrictScalars` along
`Scheme.globalSectionsRingHom k`. `finiteCurveQuotientStalk k f x` applies the
existing module stalk functor and restricts scalars along
`(X.presheaf.germ ⊤ x _).hom.comp (Scheme.globalSectionsRingHom k)`.
All their data are explicit applications of existing constructions. Their
underlying groups are exactly F(X) and F_x, so the coordinate equation in the
statement uses the ordinary presheaf germ directly. All helpers are public and
listed in `lean.declarations`.

Hypothesis-by-hypothesis translation:

| Node hypothesis | Lean |
| --- | --- |
| k is an arbitrary field | `(k : Type u) [Field k]` |
| X and Y are schemes over k | `(X Y : Scheme.{u})` and the two `Over (Spec (.of k))` instances |
| X is proper over k | `[IsProper (X ↘ Spec (.of k))]` |
| X is reduced | `[IsReduced X]` |
| X has pure dimension one | `hdim : X.IsPureDimension 1` |
| f is a k-morphism Y to X | `(f : Y ⟶ X) [f.IsOver (Spec (.of k))]` |
| f is finite and surjective | `[IsFinite f] [Surjective f]` |
| N is an open subset of X | `(N : X.Opens)` |
| N contains the generic point of every irreducible component | `hN` quantifies over `Z ∈ irreducibleComponents X` and every `x` with `IsGenericPoint x Z`, and asserts `x ∈ N` |
| The induced morphism over N is an isomorphism | `hiso : IsIso (morphismRestrict f N)`; this is the actual restriction with source `(f ⁻¹ᵁ N).toScheme` and target N |
| Neither connectedness nor nodality nor normality of Y is assumed | None of these predicates is a binder; Y is not even assumed reduced |

Clause-by-clause translation:

| Node object or conclusion | Lean |
| --- | --- |
| B is f_* O_Y, with B(U) = O_Y(f⁻¹U) | `(pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)`; `pushforward_obj_obj` is definitionally the displayed section formula |
| O_X to B is the canonical structure map | `SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom`; its component is the structure-ring map by `unitToPushforwardObjUnit_val_app_apply` |
| F is its sheaf cokernel | `finiteCurveQuotient f`, defined by `cokernel` in the abelian module-sheaf category; no sectionwise quotient is substituted for the sheaf cokernel |
| O_X to B is injective | The first conjunct is `Mono` of that canonical morphism; a mono of sheaves is sectionwise injective |
| B and F are coherent | The next two conjuncts use the recorded exact `RingedSpace.IsCoherent X.toRingedSpace` predicate |
| 0 to O_X to B to F to 0 is short exact | `ShortComplex.mk` with that structure map, its actual `cokernel.π` and `cokernel.condition`, followed by `.ShortExact` |
| The support S is finite | `∃ S : Finset X` with membership equivalent to `¬ Subsingleton ((finiteCurveQuotient f).presheaf.stalk x)` for every x |
| S consists of closed points | `∀ x ∈ S, IsClosed ({x} : Set X)` |
| Γ(X,F) to the direct sum of F_x over S is a k-linear isomorphism | An actual `LinearEquiv` from `finiteCurveQuotientSections k f` to `⨁ x : {x : X // x ∈ S}, finiteCurveQuotientStalk k f x.val` |
| That isomorphism is the germs map | For every section s and supported point x, `e s x` equals `(finiteCurveQuotient f).presheaf.germ ⊤ x.val _ s`; hence the isomorphism cannot be an unrelated vector-space isomorphism |
| Every stalk F_y is finite-dimensional over k | `∀ x : X, FiniteDimensional k (finiteCurveQuotientStalk k f x)`, including points outside S |
| H^q(X,F) is zero for q positive | `∀ q : ℕ, 0 < q → IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj (finiteCurveQuotient f))` |
| χ(X,F) equals the sum over S of dim_k F_y | First Euler equality, with `(finiteCurveQuotient f).eulerChar k` and the `Finset` sum of integer-cast `Module.finrank` |
| It also equals the sum over all closed points | Second Euler equality uses `∑ᶠ` over the subtype `{x : X // IsClosed ({x} : Set X)}` |
| The latter sum has only finitely many nonzero terms | The last conjunct is `Set.Finite` of the closed-point subtype on which that integer-cast dimension is nonzero |

Dependency interfaces read and used:

- `def-pc-euler-characteristic`: module
  `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`, declaration
  `AlgebraicGeometry.Scheme.Modules.eulerChar`; its signature and docstring
  define the integer `finsum` of signed cohomology dimensions. This existing
  Euler characteristic is retained, while the explicit vanishing clause uses
  the required ringed-space module cohomology. Their comparison is part of the
  existing project cohomology framework, not a redefinition in this delivery.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`, reducedness on all open sections (equivalent
  to the stalk condition).
- `def-sc-ringed-space-module-cohomology`:
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`,
  `AlgebraicGeometry.RingedSpace.moduleCohomology`, right derived global
  sections of module sheaves, with natural-number degree.
- `def-weil-field`: Mathlib `Field` (mathlib_match, not a missing Lean record),
  in `Mathlib.Algebra.Field.Defs`, extending `CommRing` and `DivisionRing`.
- `def-weil-finite-integral-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`,
  affineness and finite ring maps on affine opens.
- `def-weil-irreducible-components`: Mathlib match `irreducibleComponents`
  in `Mathlib.Topology.Irreducible`, the maximal irreducible subsets.
- `def-weil-pbc-exact-sequence`: import
  `Mathlib.Algebra.Homology.ExactSequence`; its recorded declaration list
  includes the exact form used here, `CategoryTheory.ShortComplex.ShortExact`
  from `Mathlib.Algebra.Homology.ShortComplex.ShortExact`, namely exactness,
  mono first map, and epi second map. These are sheaves, so categorical short
  exactness is the intended interface, rather than sectionwise surjectivity.
- `def-weil-proper-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`,
  separated, universally closed and locally of finite type (quasi-compactness
  from universal closedness gives finite type).
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `AlgebraicGeometry.Scheme.IsPureDimension`, dimension of every component,
  explicitly vacuous for empty schemes.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  a transparent abbreviation of Mathlib `SheafOfModules`. The scheme
  specialization `Scheme.Modules` is definitionally that same category;
  the existing sheaf kernel and cokernel constructions are used.
- `def-weil-surjective-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective`, surjectivity on underlying points.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, whose
  current repaired public interface includes
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`. The declaration's finite-type
  and finite-type-kernel clauses are exactly the coherence used here; the
  merely quasi-coherent/finite-type conjunction is not substituted for it.

The module imports every currently stated proof-dependency module, using plain
imports for proof-only dependencies: schematic image, schematic dominance,
Noetherian topology, invertibility, coherent higher direct images, degree-zero
sections comparison, coherent kernels/cokernels, coherent versus finite type,
zero-dimensional support, and finite-support skyscrapers. The proof dependency
`lem-trf-proper-field-invertible-coherent` has no current recorded Lean module,
so there is no import to add for it. This is a proof prerequisite, not a missing
notion in the statement. The seven-step proof docstring includes every step
of the DAG plan and the nodes each step uses.

Edge cases checked before drafting and rechecked against the final signature:

- Empty X: surjectivity is vacuous and a morphism Y to empty X forces Y empty.
  Pure dimension one is vacuous, and empty S makes all displayed spaces and
  sums zero. No nonemptiness assumption was introduced.
- f an isomorphism and N = X: the cokernel is zero and S can be empty.
- Disconnected or reducible X: generic containment quantifies over every
  component, rather than selecting a single generic point.
- Y with a finite nilpotent thickening at closed points: allowed; generic
  isomorphism still holds and the defect stalks measure the thickening.
- A closed point with nontrivial residue extension: dimensions are over k
  itself, using the germ of the base structure map, and not residue-field
  dimensions or lengths.
- q = 0 is not claimed to vanish; only `0 < q` occurs in the vanishing clause.
- Every unsupported stalk, including component generic points, is covered by
  the finite-dimensional conclusion (it is zero).
- The closed-point `finsum` cannot mask infinitely many nonzero terms because
  its finite-support assertion is stated separately.

Searches actually run (Q26 log through msearch.py):

- `leanfinder`: "Finite morphism of reduced proper curves quotient structure
  sheaf finite support germs Euler characteristic". Eight hits, concerning
  finite fibres, stalk localization, germ-injective spreading and finite
  section maps; none states the coherent quotient/germs/Euler result.
- `loogle`: `"eulerChar", "cokernel"`. Zero hits.
- `grep` in Mathlib `AlgebraicGeometry`:
  `eulerChar|finiteSupport.*cohomology|coherent.*skyscraper`. Zero hits.
- `leansearch`: "Quotient of structure sheaf by finite birational modification
  has Euler characteristic equal to sum of stalk dimensions". Eight hits,
  about structure-sheaf stalks and the unrelated incidence-algebra Euler
  characteristic; none matches this statement.
- `rg` in the read-only `lean/WeilConjectures` and `lean/Sheaf` searched
  `globalSectionsRingHom`, scalar-restricted stalks, quotient/stalk/Euler
  combinations and finite-curve-quotient names. It found the existing
  `unitToPushforwardObjUnit`, `pushforward`, `RingedSpace.moduleStalkFunctor`,
  `ModuleCat.restrictScalars` usages, and Euler/cohomology interfaces used
  above. The adelic quotient and etale finiteness hits concern other objects.
- `grep -rn` for the item id in `lean/WeilConjectures` found no match.
  `rg` for all four new declaration names in the two library source trees
  and `dag/lean_names_upstream.json` found no existing declaration.

Validation: the prescribed `scompile.py Q26
lem-trf-finite-curve-quotient-stalk-euler <module>` compiled the file in sandbox
and library modes successfully, with no errors or non-sorry warnings. Both
`autoImplicit` and `relaxedAutoImplicit` are false, all universes are explicit,
and every Lean line is at most 100 characters. The sole postponed proof is
the theorem matching this DAG node; the helper data contain no `sorry`.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
