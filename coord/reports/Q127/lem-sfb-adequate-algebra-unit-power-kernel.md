## Worker report

Q127 states `lem-sfb-adequate-algebra-unit-power-kernel` in
`Sheaf.AlgebraicGeometry.AdequateAlgebraUnitPowerKernel`, declaration
`CategoryTheory.adequateAlgebraUnit_power_kernel`. Its proof is `sorry`, as required
for stage 2. No statement correction or dependency replacement is needed.

The source was read in Alper's published PDF,
https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf,
Lemma 5.2.6, printed p.508, and Proposition 3.3.5, printed p.498. The former applies
to every quasi-coherent algebra on the base; the latter gives universal adequacy
and locally nilpotent kernel. The theorem records the requested algebraic consequences
at every scalar extension. It does not add the stronger characteristic-zero clause.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`. The commutative k-algebra is
  `(R : Type u) [CommRing R] [Algebra k R]`.
- The algebraic stack is `F : BasedCategory.{v, w} (Over (Spec (.of k)))` and
  `hF : IsAlgebraicModuliStack F`. Its independent object and morphism universes
  remain `w` and `v`.
- The morphism to Spec R is `φ : BasedFunctor F (discreteModuli (yoneda.obj
  (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))))))`. Thus it is over k,
  not an arbitrary ring map on a chosen atlas.
- The hypothesis `hφ : IsAdequateModuliSpace F hF (AlgebraicSpace.schemeSpace ...) φ`
  is exactly the recorded adequate-moduli definition applied to the actual representable
  algebraic space Spec R, including its qcqs conditions, structure isomorphism and
  universal quasi-coherent-algebra tests on each affine etale base change.
- The arbitrary commutative R-algebra is `(C : Type u) [CommRing C] [Algebra R C]`.
  The common scheme universe follows the recorded scheme and stack conventions.
- `moduliScalarSheaf φ C` is the actual tensor extension: it is the sheafification
  of the ring-presheaf pushout of the constant R algebra into the structure presheaf
  and into constant C. Ring presheaf pushouts are pointwise ring pushouts, hence tensor
  products. On affine tests this gives A tensor_R C. On nonaffine tests the associated
  sheaf is used; no false assertion about tensor commuting with all global sections
  is assumed. The left pushout leg is `moduliScalarAlgebra φ C hF.1.1`'s structure map.
- The ring D is the dependency's `moduliGlobalSectionsRing (moduliScalarSheaf φ C)`.
  `moduliScalarUnit φ C` is explicitly the right pushout leg followed by the
  sheafification unit, evaluated on constant c and assembled as a compatible family.
  Thus it is c ↦ 1 tensor c. `moduliScalarSectionsAlgebra` uses this precise ring
  homomorphism's `toAlgebra`, rather than an arbitrary C-action.
- Every commutative C-algebra is quantified as `(C' : Type (max u t)) [CommRing C']
  [Algebra C C']`. Taking t=u includes the identity extension; the max prevents
  an independent smaller test universe from making universal quantification vacuous.
- The tensor target is `C' ⊗[C] moduliGlobalSectionsRing (moduliScalarSheaf φ C)`.
  Its `algebraMap C'` is the canonical left inclusion c' ↦ c' tensor 1. The tensor
  uses Mathlib's algebra tensor product, with D's C-action fixed as above.
- The first conjunct quantifies over every c', assumes its image is zero, and asserts
  `IsNilpotent c'`. This is elementwise nilpotence, with no uniform exponent or
  nilpotence-of-the-whole-ideal strengthening.
- The second conjunct quantifies over every d', and states `∃ N : ℕ, 0 < N ∧
  ∃ c' : C', algebraMap ... c' = d' ^ N`. This is exactly the positive-power lift.
- There are no finite-generation, flatness, Noetherian, characteristic or absolute
  diagonal-separation assumptions anywhere in the theorem.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, a commutative ring and division ring.
- `AlgebraicGeometry.Spec` and `Spec.map`, Mathlib.AlgebraicGeometry.Scheme; the
  scalar construction also uses the canonical `Scheme.ΓSpecIso` and `appTop`.
- `CategoryTheory.IsAdequateModuliSpace`, Sheaf.AlgebraicGeometry.AdequateModuliSpace;
  its full definition and docstring were read, including the all-algebras affine-etale tests.
- `CategoryTheory.ModuliAlgebraSheaf`, `moduliStructurePresheaf`,
  `moduliStructureSheaf`, and `moduliGlobalSectionsRing`,
  Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra. The global ring is the pointwise
  ring of all compatible families. This existing notion is reused unchanged.
- `LinearMap.baseChange` / `TensorProduct`, Mathlib.LinearAlgebra.TensorProduct.Tower;
  `Algebra.TensorProduct` structures, Mathlib.RingTheory.TensorProduct.Basic and Maps.
- `AlgebraicGeometry.AlgebraicSpace.schemeSpace`,
  Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite, the existing representable-space
  construction for the affine target. No second definition of a scheme as a space.
- The new node uses existing `discreteModuli`, `BasedFunctor`, and `IsFibredInGroupoids`
  through StackQuasiCoherentAlgebra's imports, with `w_obj` transports rather than
  imposing definitional equality of underlying scheme objects.

The main theorem imports the stated proof dependencies with available modules:
MvPolynomial.Basic, Flat, and TensorProduct.Maps, besides the public statement
imports. The adequate affine-target criterion, affine-target base change, stack flat
scalar sections, ideal-quotient comparison, and relative-spectrum construction have
no usable Lean record yet in the read DAG. They are proof dependencies only: their
unproved statements are not required to type this theorem. No replacement or private
copy of those statements is introduced. The complete three-step proof route from the
node is in the theorem's docstring, including the map identifications after quotienting.

Edge cases checked before writing:

- C and C' may be zero rings; neither carries Nontrivial. The tensor and its unit exist,
  and zero elements are nilpotent with positive exponent.
- C'=C is allowed. The conclusion includes the original unit by the tensor unitor.
- Nilpotence is elementwise, allowing nil ideals without any common nilpotence exponent.
- Powers N=0 are excluded by `0 < N`; exponents may depend on the target element and C'.
- Polynomial presentations may have infinitely many variables, since C is unrestricted.
- Positive and zero characteristic are both permitted. No diagonal condition was added.
- Empty test categories are not ruled out by an extra assumption. A purported adequate
  moduli map in that case must still satisfy the existing structure-sheaf isomorphism.
- ULift transports put the constant rings in `max (u+1) v w`, exactly the coefficient
  universe of the recorded structure sheaf. No site-universe equality is imposed.

Searches (the exact service outputs are recorded in the new node's mathlib_searches,
and the wrapper also keeps searches.jsonl):

- LeanFinder: 'For an adequate moduli space the unit from an algebra to global sections
  of its tensor pullback has universally nilpotent kernel and lifts positive powers'.
  Eight hits about formal unramifiedness and affine spectra, no adequate-moduli theorem.
- Loogle: '"adequate"': zero hits.
- Mathlib grep: adequateModuli|adequatelyAffine|universallyAdequate|adequateHomeomorphism,
  AlgebraicGeometry: zero hits.
- Project rg of tensor/algebra and adequate names in both WeilConjectures and Sheaf:
  ordinary scheme tensor constructions, module comparisons, and the recorded adequate
  definitions; no algebra-unit power-and-kernel theorem. The exact item-id search in
  WeilConjectures returned no hit.
- LeanSearch: 'The tensor extension O_X tensor_R C of a commutative algebra on an
  algebraic stack is sheafification of the pointwise ring pushout and has canonical
  unit into global sections'. Eight hits include CommRingCat.tensorProdIsoPushout,
  CommRingCat.isPushout_tensorProduct, and module sheafification. Those supply general
  ingredients, not this stack scalar construction.
- LeanFinder: 'Tensor scalar extension of the structure sheaf on the big fppf site of
  a category fibred in groupoids with canonical algebra map to global sections'.
  Eight hits about tilde modules, module presheaf tensor, and structure sheaves;
  no matching stack scalar algebra.
- Mathlib grep moduliScalar|moduliTensor|scalarAlgebra|tensorAlgebraSheaf: zero hits.
  Matching project/DAG files concern StackQuasiCoherentSchemeRestriction's pullbacks
  of modules along based functors or FlatSingleScalar's derived module interfaces.
  Reading their declarations confirms neither defines this scalar algebra or unit.
- blueprint_refs.py search 'tensor extension' and 'tensor pullback algebra': zero matches.

## New nodes

`def-sfb-stack-scalar-algebra` supplies the genuinely missing construction in
`Sheaf.AlgebraicGeometry.StackScalarAlgebra`. It constructs structural pullback on
scalar rings, its natural transformation, the tensor presheaf as a pushout, its
associated ring sheaf and structure-algebra map, and the canonical unit into the
existing global-section ring. Its only postponed theorem is
`CategoryTheory.moduliScalarMap_naturality`, the naturality property explicitly
included in the definition node's statement, with a source and complete proof
in its docstring. All data are real constructions: ring maps, pushout, sheafification,
and compatible families; no data are selected from a mere existence statement.
The sheafification instance is constructed from the existing essentially-small-site
API with explicit universes. Searches above found no existing node or declaration
for this constant-algebra extension, and Alper Lemma 5.2.6 supplies its source.

## Second reading by Q127

This is a second pass by the same worker; no separate agent was started, as the
assignment forbids that. The maintainer's independent delivery review remains required.
I re-read the node and both modules, checked every binder against the correspondence
above, and checked the new node too. In particular the adequate-moduli hypothesis uses
the recorded predicate, the target is representable Spec R, D uses all compatible
families, the C-action comes from the constructed right pushout leg, the scalar
extension tests include C'=C and zero rings, and kernel nilpotence is elementwise.
During compiler-guided checking I corrected the ULift universe argument order and
the naturality equation orientation; neither alters the mathematical statement.
There is no statement correction, omitted clause or disputed assertion.

Validation: both delivered modules passed `scompile.py` separately in dependency
order against the live server library. The delivery dry run passed preflight and
all compilation at commit 7c371abe681. Its initial metadata check required the
current new-node `import_flags` key; an empty list was added and the two adjacent
node citations were separated into individual bracketed ids. No Lean or mathematical
statement changed in that metadata repair. Only expected sorry warnings are permitted.
