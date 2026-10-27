## Worker report

The delivery states Stacks 0DZ4 as
`Algebra.SquareZeroClasses.nonempty_completionLinearEquiv` in
`Sheaf.RingTheory.ExalCompletionSmoothComplement`. Its sole theorem has proof `sorry`.
It additionally defines actual marked square-zero algebra extensions and their classes in
`Sheaf.RingTheory.SquareZeroAlgebraClasses`. All definition data are explicit. No object is
chosen from a postponed existence theorem.

Clause-by-clause correspondence:

- Field k: `(k : Type u) [Field k]`.
- Finite-type commutative k-algebra B: `[CommRing B] [Algebra k B] [FiniteType k B]`.
- Ideal J: `(J : Ideal B)`.
- Smooth on the complement of V(J): `hsmooth` quantifies over spectrum points outside
  `PrimeSpectrum.zeroLocus (J : Set B)` and supplies an open neighbourhood on which the
  structure morphism is `AlgebraicGeometry.Smooth`. This is exactly smoothness at every
  point of that open complement, with no assumption at points of V(J).
- Finite B-module N: `[AddCommGroup N] [Module B N] [Module.Finite B N]`.
- Completed ring and module: Mathlib `AdicCompletion J B` and `AdicCompletion J N`, with
  its existing completed-ring module action. The latter is used in the target extension.
- Exact extension 0 -> N -> E -> B -> 0: `Extension.extension` is the existing Mathlib
  `Algebra.Extension` (surjective quotient); `i`, `injective`, and `exact` specify the
  additive kernel. `square_zero` and `action` state precisely the square-zero condition
  and the required induced B-action. No B-algebra structure on E is assumed.
- Isomorphisms induce identity on N and B: the two equations in `Isomorphic`.
  `Classes` is `Quot Isomorphic`; isomorphism is already an equivalence relation, so
  taking its equivalence closure does not change the class relation. The chosen set
  section in Mathlib's Extension is ignored by isomorphisms and does not change classes.
- Baer addition: `fiber` is Mathlib's algebra equalizer of the two quotient maps on
  E x F. `IsBaerSum` is a map from this fibre product over B whose kernel map is addition.
  Such a map to an extension gives the coefficient pushout: it is surjective by lifting
  the quotient and then correcting the kernel; its kernel consists exactly of pairs
  (i(n),i(-n)). Thus the relation determines the usual Baer class, without extra choices.
- Natural k-scalar multiplication: `IsScalarPushout` is the extension map with kernel
  map n |-> algebraMap k B a • n. Maps of extensions characterize coefficient pushout
  (equivalently use the universal pushout and the elementary isomorphism criterion for
  an extension map inducing identities on kernel and quotient).
- Natural abelian group and vector space structure: `sourceGroup`, `sourceModule`,
  `targetGroup`, `targetModule`, and the two `IsNaturalModule` fields in
  `CompletionLinearEquiv`. These are conclusions, not additional hypotheses.
- Canonical completion-induced linear isomorphism: `linearEquiv` is the linear
  equivalence for precisely those structures. The `completion` field gives its graph
  on every pair of representatives: equality holds iff `IsCompletion J E F`.
  In `IsCompletion`, the witness is an algebra isomorphism from the actual completion
  `AdicCompletion (J.comap E.p.toRingHom) E.extension.Ring` to F's middle algebra.
  The first finite-quotient equation fixes the quotient map; the second fixes the
  kernel injection. Every level and every representative are quantified. Quotient
  projections are surjective and jointly injective on compatible sequences, so these
  equations specify exactly the completed maps, not an arbitrary map on classes.

Dependency declarations read and used:

- `def-weil-field`: Mathlib.Algebra.Field.Defs, `Field`.
- `def-weil-affine-spectrum`: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `def-sbc-smooth-morphisms`: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  `AlgebraicGeometry.Smooth` (read class and its affine-local docstring).
- `def-weil-finitely-generated-module`: Mathlib.RingTheory.Finiteness.Defs,
  `Module.Finite` (finite generation of top).
- `def-weil-pbc-adic-completion`: Mathlib.RingTheory.AdicCompletion.Basic,
  `AdicCompletion`; its ring, algebra and completed-module structures are in
  Mathlib.RingTheory.AdicCompletion.Algebra.
- New definition dependency: Sheaf.RingTheory.SquareZeroAlgebraClasses,
  `Algebra.SquareZeroClasses.Classes` and the listed marked-extension operations.

All already recorded proof dependencies are imported privately, including the finite
polynomial resolution, cotangent coherence, polynomial differentials, ring pseudo-coherence,
completion Noetherianity and exactness/completeness/tensor modules. The four proof nodes
`lem-sfb-cotangent-ext-smooth-support`, `lem-sfb-supported-complex-ext-completion`,
`lem-sfb-ring-square-zero-extension-classification`, and
`lem-sfb-finite-square-zero-adic-thickening` currently have no recorded Lean declaration;
their proof steps remain in the theorem docstring and no replacement is assumed.

Edge cases checked before writing: J=0 gives completion along the square-zero kernel
on middle algebras, hence the original extension; N=0 has the unique trivial extension;
J=B forces B smooth everywhere and all completed objects zero, so the asserted comparison
reduces to formal smoothness splitting every extension. B=0 forces N=0 and exactness forces
E=0, and is allowed. No characteristic restriction, locality, proper ideal, flatness,
nonzero B, or extra finiteness on the completed base is imposed. All test objects live in
one arbitrary explicitly bound universe u, the usual common universe for rings and their
modules; `Classes` itself lives one universe higher and is not forced small. Every actual
extension of these rings/modules can be transported into that common universe. Level n=0
is the zero quotient and is included; levels n>=1 carry the information. No noncanonical
ring/module instance is chosen.

Searches: msearch leanfinder “Square zero algebra extension classes unchanged by adic
completion away from a smooth locus” returned formal-smooth lifting and algebra extensions,
not this theorem; loogle “Exal, Algebra.Extension, AdicCompletion” returned unknown Exal/no
hits; msearch grep “Exal|SquareZeroExtension|square.zero extension” in RingTheory returned
no hits. The new node preserves the full outputs of the additional LeanSearch and
LeanFinder queries for marked classes and their Baer/scalar operations. LeanSearch returned
Module.Baer.ExtensionOf (module injectivity) and TrivSqZeroExt (only split extensions);
LeanFinder returned only TrivSqZeroExt lifts. Read Mathlib's Algebra.Extension full signature:
it supplies a surjective algebra extension, but no prescribed kernel module or class set.
Project rg over WeilConjectures and Sheaf found split algebra, deformation, and sheaf
extension frameworks only. The sheaf extension data use sheaves on a space and are not
ring extension classes. The CompletionReflectsFlatLiftability module only mentions Exal in
its proof docstring. grep of the item id in WeilConjectures found nothing. Searches of
upstream names found no collision. `blueprint_refs.py search Exal` returned zero blueprint
nodes; DAG definition-node searches found sheaf/scheme variants, not ring extension classes.
The unstated classification theorem is a proof dependency, not a definition record.

Validation: both modules compiled separately via scompile.py in dependency order without
errors or warnings. No statement correction, dependency-record repair, or dispute.

## New nodes

`def-sfb-square-zero-algebra-classes` defines the actual marked ring extensions, their
isomorphism quotient, and operation graphs for Baer addition and scalar pushout. Its source
is the Exal notation immediately before Stacks 0DZ4. It does not assert existence of the
natural module structure (that is part of the assigned theorem). It reuses Mathlib's
Algebra.Extension for the middle algebra and surjection and AlgHom.equalizer for the fibre
product. The three search kinds and project/DAG searches above establish that no existing
notion defines this class set. No new proof node is introduced.

## Second reading by Q77

Author's second reading; the dispatcher's maintainer supplies the independent review.
Reopened the node and both final modules. The five original hypotheses occur literally as
Field, FiniteType, Ideal, smooth open neighbourhoods outside zeroLocus, and Module.Finite.
In particular N's module structure is over B, whereas the completed kernel is over the
completed B, so the statement has not substituted coefficient Ext or a restricted class
of continuous extensions. I checked both ends of the middle-algebra comparison: the
quotient equation is from e(z) to the quotient of E.p(x); the injection equation uses
e.symm(F.i(z)) to the quotient of E.i(x). These orientations give the original markings.
The iff graph includes every representative, so isomorphism changes preserve the result.
Baer addition and scalar pushout are explicitly required on both class sets, and the
linear equivalence uses those exact supplied instances. No tautological or hollow smoothness
hypothesis has been inserted. The definition module has no theorem/sorry, and the item
has exactly one postponed theorem with all five DAG proof steps. Found and fixed a missing
private import of the already stated finite polynomial resolution before final validation.
All new declarations have source/blueprint docstrings. No node statement was changed.
