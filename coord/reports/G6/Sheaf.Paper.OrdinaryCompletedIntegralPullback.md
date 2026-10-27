## What changed

The assigned module now proves the existence of its ordinary total left derived pullback,
the invertibility of its computation counit on flat-term K-flat representatives, and the
existence and uniqueness of its generator-normalized strict quotient augmentation.

The derived proof presents module inverse image algebraically, composes its canonical
adjunction with explicit scalar extension, identifies the right adjoint by the coefficient
adjunction equation, and transports the independent-universe derived-pullback theorem across
uniqueness of left adjoints. Uniqueness of total left derived functors transports the good
representative computation to the exact counit used by the published construction. The final
ordinary constructibility/completion implication remains the one open declaration reported
below; no unproved replacement theorem was introduced.

The augmentation proof transports the existing slice augmentation across the ordinary/ambient
module-pullback comparison and the existing strict pullback-tower isomorphism. Its formula is
checked on the actual adjunction-unit sections. Injectivity of the module-adjunction Hom
bijection proves uniqueness degree by degree, level by level. The proof does not assume that
unit sections generate sections on each target-site object.

Only proof imports and proved private helpers are added. Public signatures, public definition
bodies and public imports are unchanged. The existing construction and augmentation nodes now
record the implementation route; the derived-construction node records its derived existence
and good-complex computation proof. The final theorem and its main node are unchanged. Local instance controls are documented in
coord/changes/G6-ordinary-derived-proof-elaboration.md, including the 19-consumer census.

## Proved and sorry left

Closed three of the original four holes:

- WeilConjectures.ordinaryIntegralPull_hasLeftDerived.
- WeilConjectures.ordinaryIntegralPullComplexCounit_isIso.
- WeilConjectures.ordinaryIntegralQuotientAugmentation_existsUnique.

One original hole remains: WeilConjectures.ordinaryCompletedIntegralPullback, attached to
lem-tw-ordinary-completed-integral-pullback. No holes are added and no statements are split off.
No definition contains sorry. This is a partial delivery for a module with several holes.
The complete assigned file compiled cleanly through lcompile.py in 31.3 seconds after the
explicit naturality and identity-composition transport corrections; no warning remains.

## No longer needed

No original import or module is removed. The final constructibility/completion theorem is
unchanged, so its planned dependencies remain needed. Nothing is claimed globally pruned.

For the quotient augmentation itself, the proof reuses the existing normalized ambient tower
comparison instead of rebuilding the sheaf tensor universal property, inverse-image tensor
comparison, products and mapping cone. Its direct proof dependencies are now only

def-sf-ordinary-integral-pullback-construction, def-pur-integral-derived-operations, and
lem-pur-integral-ambient-operation-models.

The following old direct proof dependencies are not used separately by this augmentation
proof (some remain transitive prerequisites of the reused constructions):

def-pur-sheaf-tensor-product; def-weil-abstract-derived-category; def-weil-category-product;
def-weil-completed-integral-coefficients; def-weil-derived-limit;
def-weil-proetale-inverse-image; def-weil-signed-mapping-cocone-functor;
def-weil-tower-transition-endomorphism; lem-pc-sites-sheaf-tensor-bilinear-universal;
lem-pur-proetale-inverse-image-tensor-comparison;
lem-weil-pbc-ringed-topoi-module-adjunction;
lem-weil-proetale-countable-products-exact.

## Where the brief, the DAG or earlier work was wrong

The node's derived-construction attachment had no proof steps. Its implementation needs the
independent object/morphism/coefficient universe theorem, not a same-universe specialization.
The explicit tensor-functor universe arguments are necessary: leaving these inferred can pick
a smaller coefficient universe and create stuck max-universe constraints.

The final planned stratified-model dependency cannot simply be imported by the assigned
module: Sheaf.Paper.OrdinaryPullbackStratifiedModels already imports this module for the
ordinary construction. Its local-model interface also differs from the characterization's
slice/inverse-image-ring interface. The remaining theorem therefore still needs explicit
interface bridges and an import-cycle repair; the three closed obligations do not assert
that this final mathematical step has been proved.

The launcher resumed this same sandbox several times. The claim records its original start
at 2026-10-23T12:26:59Z; the resumed .budget metadata records start 1792769022.2526486.
The worker did not edit budget metadata or launcher scripts. Dispatch marker files present
are .brief2, .brief3, .brief4 and .brief5; no attempt identifier was supplied in the resume
messages. These metadata differences did not justify leaving any newly added hole.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
