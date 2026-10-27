## Worker report

Sheaf.AlgebraicGeometry.PowerLiftingQuotientSubmersive states the single theorem
AlgebraicGeometry.SchemeAction.power_lifting_quotient_submersive with sorry.
There are no new definitions or instances. The accepted mathematical statement
and six proof steps are unchanged; the encoding of equivariance is now at scheme
level as requested in the return of aa4b3e03dd1f.

Every hypothesis and clause is rendered as follows:

- `k : Type u` and `[Field k]` give the field.
- `H : Over (Spec (CommRingCat.of k))` with `[GrpObj H]` gives a k-group scheme.
  `[IsAffineHom H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]`
  gives affine and finite type, with no smoothness assumption.
- The hypothesis quantifies over arbitrary `D D' : Type u` with commutative-ring
  and k-algebra structures and `ModObj H (affineActionScheme k D)` and its D'
  counterpart. No finite-generation hypothesis occurs here. Unit and associativity
  of scheme actions dualize to counit and coassociativity on affine coactions.
  Inversion exchanges left and right conventions, preserving invariants and maps.
- `f : D →ₐ[k] D'` and `Function.Surjective f` are the surjective algebra map.
  Equivariance is expressed by existence of
  `s : affineActionScheme k D' ⟶ affineActionScheme k D` with
  `s.left = Spec.map (CommRingCat.ofHom f.toRingHom)` and
  `Nonempty (IsModHom H s)`. Its underlying scheme map is pinned exactly to Spec f,
  not an arbitrary morphism. Since f is a k-algebra homomorphism, Spec f is over
  Spec k: the over-map equation is the contravariant image of f.comp_algebraMap.
  An Over morphism is determined by its underlying scheme morphism, so this is
  exactly equivariance of f, with no additional hypothesis or choice. IsModHom
  says action composed with s equals H acting on s followed by the target action;
  it is equality of scheme morphisms, retaining all infinitesimal test objects.
  Nonempty merely turns the Type-valued IsModHom structure into a proposition.
- `b : affineInvariants k D' H` is an element of the actual invariant equalizer.
  `∃ (n : ℕ) (_ : 0 < n) (a : affineInvariants k D H), f a = (b : D') ^ n`
  is precisely positive-power lifting from D^H.
- E is a commutative k-algebra with `[Algebra.FiniteType k E]` and its rational
  H-action `[ModObj H (affineActionScheme k E)]`.
- `L : Type v` with `[CommRing L] [Algebra (affineInvariants k E H) L]` is an
  arbitrary invariant-ring algebra in an independent universe. There is no
  flatness, Noetherianity, finite-generation or reducedness assumption.
- Mathlib's `Algebra.ofSubsemiring` supplies the algebra of the actual invariant
  subring on E. Its algebra map is the inclusion by `Algebra.algebraMap_ofSubring`.
  The source of `includeRight` is L, its target is E tensor_(E^H) L, and it sends
  l to `1 ⊗ₜ l`. Its `PrimeSpectrum.comap` is exactly the required base-changed
  affine-spectrum map; `PrimeSpectrum.continuous_comap` gives its continuity.
- The first conjunct asserts surjectivity. The second, quantified over every
  `V : Set (PrimeSpectrum L)`, is exactly `IsOpen V ↔ IsOpen (comap ... ⁻¹' V)`.
  There is no assertion that the map is open or that invariants commute with
  arbitrary base change, and no finite-generation assumption on E^H.

Dependency declarations and sources read:

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`, lines 169--180.
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, `GrpObj`, lines 41--48,
  in Over Spec k. WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents
  this exact specialization in its module docstring.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, `Spec` and
  `Spec.map`, lines 469--480.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `LocallyOfFiniteType`, lines 39--46, and Morphisms.QuasiCompact, `QuasiCompact`,
  lines 38--46.
- def-sfb-affine-action-quotient-stack: Sheaf.AlgebraicGeometry.AffineActionQuotientStack,
  `AlgebraicGeometry.affineActionScheme`, lines 287--291. Its definition has no
  smoothness or finite-generation restriction; the stronger assumptions of the
  quotient-stack wrapper are not used.
- def-sfb-affine-action-invariant-spectrum:
  Sheaf.AlgebraicGeometry.AffineActionStackPresentation,
  `AlgebraicGeometry.SchemeAction.affineInvariants`, lines 75--78. The full node
  statement and its six-declaration lean record were read. It owns the equalizer
  and coordinate constructions with no smoothness or finite-type restrictions.
- Mathlib.CategoryTheory.Monoidal.Mod: `ModObj`, lines 52--65, and `IsModHom`,
  lines 184--189, full signatures, action equations and docstrings read.
- Mathlib.Algebra.Algebra.Basic: `Algebra.ofSubsemiring`, lines 96--104, and
  `Algebra.algebraMap_ofSubring`, lines 116--118, provide the standard structure.
- Mathlib.RingTheory.TensorProduct.Basic: `Algebra.TensorProduct.includeRight`,
  lines 323--331. Mathlib.RingTheory.Spectrum.Prime.Topology: `comap` and
  `continuous_comap`, the latter at line 335.

The module publicly imports the existing equalizer's module and prime-spectrum
module. The already-stated proof dependencies FlatAffineActionStackPresentation
and AdequateModuliUniversallySubmersive are imported privately. The other two
nontrivial proof dependencies, flat-affine-action-algebra-descent and
global-power-lifting-adequacy, still have no Lean record and are not needed to type
this statement. Affine spectra and fibre products are available through imports.
The theorem's docstring retains all six accepted proof steps and their node names.

Source checked in the original delivery and retained:
https://arxiv.org/html/1005.2398v3, Lemma 9.2.5(3), Theorem 9.1.4 and Remark 9.1.5,
Theorem 5.3.1(1)--(3), and the published nonsmooth fppf-presentation interface.
The source agrees with the node. No statement correction or dispute.

Edge cases reread after the repair: trivial H gives the identity quotient;
E = 0 and L = 0 permit empty spectra, with no Nontrivial instance excluding
these cases. Nonsmooth groups such as alpha_p remain included. There is no
characteristic restriction. The exponent remains strictly positive. D,D' can be
infinitely generated and live in the scheme universe u; the hypothesis is never
restricted to a lower independent universe. L has independent universe v.
IsModHom is scheme-level equivariance, so nonreduced groups and test schemes
remain visible. The pinned Over map exists for every k-algebra homomorphism,
so the new formulation adds no obstruction beyond equivariance.

Searches actually run in the initial dispatch, retained for this repair:

- msearch LeanFinder: "An affine invariant quotient is universally submersive if
  powers of invariant elements lift across all equivariant surjections" returned
  generic representation and quotient results, no exact theorem.
- msearch LeanSearch: "Power lifting invariant elements implies the affine
  invariant quotient is universally submersive" returned eight hits, including
  Scheme.Hom.liftQuotient, Rep.mkQ_hom and Submodule.mapQ_pow, no exact match.
- msearch Loogle: `IsQuotientMap, PrimeSpectrum.comap` gave no exact match;
  `"IsQuotientMap", "PrimeSpectrum"` returned the generalizing/specializing
  prime-spectrum quotient-map criteria, not the invariant-quotient theorem.
- msearch grep: `Coaction|coaction|geometricallyReductive|powerLifting` in Mathlib
  found no invariant-quotient theorem; the narrower AlgebraicGeometry query
  `powerLifting|power_lifting|universallySubmersive` returned zero hits.
- Local rg searched both Lean source trees and dag/lean_names_upstream.json for
  coactions, rational actions, power lifts and invariants, and the exact item id
  in WeilConjectures. It found the existing equalizer interface, not this theorem.
- Repair searches read the current owning definition nodes and declarations,
  Mathlib IsModHom, and Mathlib Algebra.ofSubsemiring/algebraMap_ofSubring.
  The latter confirms the duplicated instance is unnecessary.

Validation of the repaired file: scompile.py compiled both sandbox and library
modules cleanly (8.7 s and 5.2 s reported), with no errors or non-sorry warnings.
No local compiler or global build was run.

## Returned-head repair

Returned immutable head: aa4b3e03dd1f. All points in L's entry are repaired:

1. H2, invariant ownership: removed lem-sfb-affine-action-stack-presentation from
   stmt_deps and cited def-sfb-affine-action-invariant-spectrum for affineInvariants.
2. H2, unowned tensor-coordinate definitions: chose the explicitly authorized
   scheme-level alternative. Removed every use of affineTensorCoaction,
   affineGroupCoordinates and the tensor-product comparison from the statement;
   used Mathlib IsModHom on the uniquely pinned Spec f morphism instead. No new
   definition node is necessary because this is already Mathlib's notion.
3. H2, affineActionScheme: added def-sfb-affine-action-quotient-stack to stmt_deps.
4. H4, duplicate algebra instance: deleted affineInvariants.algebra completely;
   the unchanged tensor-base-change conclusion compiles using Mathlib's instance.

The sandbox node was reconstructed from current main, preserving its statement,
accepted proof, proof_deps and all other fields; only lean and the two required
statement dependencies differ. No dependency node or source-library file changed.
The return's accepted mathematical content is preserved.

## Second reading by NB

This worker reopened the repaired module and current node for a separate pass.
The dispatcher forbids starting another agent; the maintainer performs the
independent review. H's three finiteness/affineness binders and GrpObj remain;
D,D' have no finite-generation restriction; f is a surjection; the morphism s is
exactly Spec f and IsModHom imposes full equivariance; b is in D'^H, a in D^H,
and n > 0. E alone is finite type. L remains arbitrary in universe v, and both
surjectivity and the open-set equivalence are identical to the returned version.
There is one theorem with sorry and no instance or helper definition. The two
added stmt_deps own precisely the existing notions used, and the theorem node
formerly added only to own definitions is absent. No mismatch remains.
