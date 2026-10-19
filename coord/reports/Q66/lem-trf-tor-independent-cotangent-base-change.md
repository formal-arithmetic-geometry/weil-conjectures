## Worker report

The module `Sheaf.RingTheory.TorIndependentCotangentBaseChange` states
`Algebra.CotangentResolution.isPolynomialResolution_tensor_of_torIndependent`,
with its sole theorem proof `sorry`. The two helper definitions construct the
base-changed ring arrow and the augmented simplicial tensor algebra with real
data, using categorical pushouts. These are operations on the owning node's
objects, not new independent notions. Every declaration is listed in `lean.declarations`.
No node statement or dependency record is changed.

Source read: Stacks `cotangent.tex`, Tag 08QP, proof of
`lemma-flat-base-change` (lines 958–981), and Tag 08QI,
`remark-resolution` (lines 666–704). The former explicitly uses the free
alternating-face resolution to identify the specified tensor augmentation with
the derived-to-ordinary comparison. The latter gives exactly the degreewise
polynomial, degreewise surjective, associated-complex quasi-isomorphism criterion.

Hypothesis and conclusion correspondence:

- The commutative ring map A → B is `f : Arrow CommRingCat.{u}`: A is
  `f.left`, B is `f.right`, and the map is `f.hom`. The second map A → A'
  is `α : f.left ⟶ S`, with `S : CommRingCat.{u}`. Thus all three rings and
  the two homomorphisms are explicitly bound. Choosing a common ambient ring
  universe imposes no mathematical smallness condition on a finite collection
  of rings. The polynomial variable sets retain that same unrestricted universe.
- B' = B tensor_A A' is the ring pushout `pushout f.hom α`, with its A'
  structure `pushout.inr f.hom α`, exposed by `tensorBaseArrow f α`.
  This is the categorical tensor-product model, canonically identified with
  the algebraic tensor product by Mathlib's `CommRingCat.isPushout_tensorProduct`
  (`Mathlib.Algebra.Category.Ring.Constructions`, lines 116–124).
- The augmented simplicial A-algebra is exactly the dependency's
  `P : Algebra.CotangentResolution.Augmentation f`.
  `hP : IsPolynomialResolution P` retains all three defining clauses: each term
  is isomorphic over A to `MvPolynomial E A`, each augmentation is surjective,
  and `QuasiIso (additiveAugmentation P)` is the alternating-face complex
  quasi-isomorphism to B[0]. No private polynomial-resolution predicate occurs.
- Ordinary scalar extension is the existing
  `ModuleCat.extendScalars α.hom`, on complexes via
  `.mapHomologicalComplex (.up ℤ)`. This is the tensor construction of
  `def-weil-module-base-change`, in Mathlib's scalar-first ordering.
- Derived extension is expressed by an arbitrary universal pair `(L, ε)`:
  `L : DerivedCategory (ModuleCat f.left) ⥤ DerivedCategory (ModuleCat S)`,
  and the displayed natural counit `ε` with `hL : L.IsLeftDerivedFunctor ε ...`.
  These are presentation data for the canonical derived functor, not an extra
  ring hypothesis. The one-point dependency explicitly transports the sheaf
  universal pair to precisely this ordinary scalar-extension universal pair,
  preserving its counit. Universality determines it up to its unique
  counit-compatible isomorphism, so the statement applies to that transported
  pair without making an arbitrary choice from an existence theorem. Its
  localization universes `wA` and `wS` are independent.
- B[0] is `singleFunctor ... 0` applied to the underlying A-module of B:
  `(ModuleCat.restrictScalars f.hom.hom).obj (ModuleCat.of f.right f.right)`.
  The hypothesis `hTor : IsIso (ε.app (... B[0] ...))` is the canonical
  derived-to-ordinary comparison being an isomorphism in D(A'), equivalently
  a quasi-isomorphism of representatives. It is not existence of some
  isomorphism between the two objects, and it is not an assumed flat ring map.
  Its target is ordinary extension of B[0], canonically B'[0].
- The conclusion is exactly
  `IsPolynomialResolution (tensorAugmentation P α)`. Pointwise pushouts in the
  simplicial functor category have terms P_n tensor_A A'. The structure map
  is the second pushout injection. The augmentation is `pushout.desc` from
  `P.augmentation` followed by B → B' and the coefficient map A' → B'. Its
  compatibility is checked from `P.triangle` and `pushout.condition`.
  Thus the conclusion keeps the given tensor augmentation, including the
  maps on all simplicial operators, and contains all three resolution clauses.

Dependency declarations read and used:

- `Sheaf.RingTheory.CotangentResolutionCoherence`:
  `Algebra.CotangentResolution.Augmentation`, `negativeComplex`,
  `additiveAugmentation`, `IsPolynomialResolution`, and `exists_coherence`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; the localization inverts exactly
  the cochain quasi-isomorphisms.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`, read
  with its scalar-first tensor convention; scalar extension on complexes is
  the compatible existing `ModuleCat.extendScalars` construction.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, including `E`, `obj_eq`,
  `map_eq`, `T`, `ε`, `universal`, `computes`, and the existence theorem.
  The module uses this recorded interface as the origin of the transported
  universal pair, with no second sheaf or ordinary derived-functor definition.
- `Sheaf.TraceFormula.OnePointDerivedRingIdentification`:
  `CategoryTheory.OnePointDerivedRingIdentification` and
  `one_point_derived_ring_identification`; read especially `scalarExtension`
  and its existing `singletonDerivedScalarComparison` predicate, which
  intertwines the universal counits and ordinary extension of scalars.
- The proof plan imports the recorded `BoundedFlatKFlat`,
  `KFlatScalarExtensionCounit`, `LeftDerivedFromResolvingClass`, the upstream
  `MorphismProperty.kFlat`, and Mathlib's polynomial scalar-extension module.
  Their exact statements were read; no proof-only assumptions are added to
  the theorem. The complete six-step node proof is in the theorem docstring.

Edge cases checked before and after drafting: zero rings and zero modules;
identity scalar extension; zero-variable and infinitely many variable
polynomial algebras; non-flat A → A' when the specified B is Tor-independent;
all negative complex degrees and degree zero, with zero positive terms;
independent source and target derived morphism universes. None is excluded.
In particular there is no finiteness, flatness, nonzero-ring, or chosen-standard-
resolution hypothesis. The derived comparison must be its natural counit;
replacing it by an arbitrary isomorphism would lose the augmentation and was
explicitly avoided. No statement dispute or source correction was needed.

Searches actually run with `msearch.py Q66 lem-trf-tor-independent-cotangent-base-change`:

- LeanFinder: `A polynomial simplicial resolution remains a resolution after Tor independent base change`.
  Eight results on projective/module/representation resolutions and formal
  smoothness, none stating the given simplicial polynomial-resolution theorem.
- Loogle: `"cotangent", "baseChange"`. Twelve results including
  `KaehlerDifferential.cotangentComplexBaseChange`, which source inspection
  shows is a map between tensor modules in a presentation, not this theorem.
- grep, RingTheory: `cotangentComplexBaseChange|torIndependent|simplicial.*baseChange`.
  Fourteen results, all the naive cotangent map and smoothness applications.
- LeanSearch: `Polynomial simplicial resolutions preserved by Tor independent base change`.
  Eight results, including smooth/unramified base change and `Algebra.IsPushout.cancelBaseChange`;
  none states the resolution assertion.
- `rg` on the upstream `WeilConjectures` and shared `lean/Sheaf` for
  `torIndependent|cotangentComplexBaseChange|IsPolynomialResolution` found
  the dependency predicate and unrelated Tor-independent module-complex results.
  The latter require module K-flat/Tor hypotheses and do not assert polynomial
  simplicial base change, so none is an exact existing match.
- `grep -rn 'lem-trf-tor-independent-cotangent-base-change'` on upstream
  `WeilConjectures` found no declaration. Additional searches for simplicial
  tensor/base-change augmentation found no existing construction of this
  augmented simplicial tensor algebra.

Validation: the prescribed scompile wrapper compiled the module in sandbox
and library-module modes with no errors or warnings. Subsequent import changes
are recompiled before delivery. The only postponed assertion is the named
main theorem; all helper data and their coherence laws are fully constructed.

## Second reading by Q66

Self-check performed by reopening the node and the delivered module. This
worker was explicitly instructed not to start other agents; the maintainer's
independent delivery reader remains the independent review.

The main check was that the conclusion refers to the actual tensor augmentation.
The simplicial pushout is over the same constant A-algebra used in P.base,
and pushout.desc uses P.augmentation itself. Its triangle law is therefore
exactly the original augmentation triangle after tensoring. The original
three-clause predicate is reused unchanged. The Tor hypothesis names the
universal counit at the underlying A-module B in degree zero, rather than an
arbitrary arrow. The separate localization universes exclude no case and do
not force site object and morphism universes to coincide. No hypothesis or
clause mismatch was found in this second reading. During elaboration, the
NatTrans equality proof was corrected to compare component morphisms rather
than underlying ring elements; the mathematical definitions and statement
were unchanged.
