## What changed

Replaced the sole hole of `Sheaf.Paper.SupportedTensorIsomorphismTransport` by a
complete combination proof from three named comparison calculations. The existing
public definitions and theorem signature are unchanged. Each new calculation has
one new module and its own DAG node, with source and full proof in words.

The main proof constructs invertibility directly from the four actual transport
factors. Its private `restriction_injective_of_iso` proves a stronger elementary
fact: for any adjunction J left adjoint to U, U is injective on arrows from E
whenever E is isomorphic to J(P). Precompose with that isomorphism's inverse and
use the adjunction Hom bijection. Thus full faithfulness and invertibility of the
open unit are unnecessary for both uniqueness arguments. The existing packaged
`DerivedCategory.canonicalTensorSymmetry` supplies an isomorphism from the reversed
source to the original source, so the same private injectivity proof applies. This
does not require identifying its hom with the separately specified sigma: the
signed-unit calculation concerns that exact sigma and supplies the required unit
equation. Injectivity gives its uniqueness. The identity-unitor calculation
concludes the final clause. The proof-only import
`Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry` supplies the packaged symmetry.
The existing symmetry node `lem-kun-tensor-sym` is used through the proved
general-category construction in its module, specialized to pro-etale sheaves;
no etale/pro-etale equivalence is asserted. Directly elaborating the raw derived
braiding was expensive; using its existing
packaged interface removes that comparison entirely.

The original seven-step plan remains below the same unit route: the calculations
split off Steps 1/3/4, Step 6, and the comparison coherence of Step 7. They are not
copies of the original conjunction or its hypotheses. In particular they require
no purity setting, no separated/finite-type schemes, and no invertibility of the
input arrow; the signed calculation has only one open and no Cartesian square,
and the identity calculation assumes no unit equation at all.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.FiniteOpenProduct.supportedTensorIsomorphismTransport`
(node `lem-pur-supported-tensor-isomorphism-transport`) by decomposition.
The item's module has zero holes. The private injectivity helper is fully proved.

Added three holes, one in each of the following public theorems:

- `WeilConjectures.FiniteOpenProduct.supportedTensor_cartesian_unit`, node
  `lem-pur-supported-tensor-cartesian-unit`, module
  `Sheaf.Paper.SupportedTensorCartesianUnit`.
- `WeilConjectures.FiniteOpenProduct.supportedTensor_signed_unit`, node
  `lem-pur-supported-tensor-signed-unit`, module
  `Sheaf.Paper.SupportedTensorSignedUnit`.
- `WeilConjectures.FiniteOpenProduct.supportedTensor_identity_unitor`, node
  `lem-pur-supported-tensor-identity-unitor`, module
  `Sheaf.Paper.SupportedTensorIdentityUnitor`.

Counts: one original hole closed, three lower holes added; this is a decomposition,
not a net proof gain. Every remaining proof is exactly `:= by sorry`; no definition
contains a hole. The assembled main theorem compiled successfully in 25.6 seconds during profiling;
the three new statements also compiled individually. Profiling options were removed
before the delivery checks. Final compilation results are recorded by the delivery tool.

## No longer needed

Removed the direct proof import `Sheaf.Paper.DerivedPullbackTensorIso` from the
item. Its recorded finite comparison is stated in the intrinsic coefficient
presentation, whereas this module uses arbitrary fixed scalar coefficients and
`FiniteOpenProduct.tensorPullIso`. Applying that theorem directly does not type
as the required comparison coherence. The new steps retain its mathematical
coherence argument as a dependency; no global withdrawal of that module is claimed.

The parent proof no longer directly uses the old proof dependency
`lem-sf-open-tensor-normalization`; its normalized beta calculation now belongs to
the Cartesian calculation. That dependency remains needed below the new nodes.
No existing module is withdrawn, and no unit statement or realized step is bypassed.

The full-faithfulness/recovery-of-interior-maps argument originally proposed in
Step 5 is unnecessary: adjunction Hom injectivity proves the result immediately.
No separate lemma or module for that argument is introduced.

## Where the brief, the DAG or earlier work was wrong

The node's prose treats tensor/pullback composition, signed braiding, and identity
coherence for these exact fixed-scalar derived maps as available directly from
`derivedPullbackTensorIso`. Its Lean signature instead concerns intrinsic finite
coefficient categories indexed by l, E and n, with additional coefficient data.
The existing cochain coherence theorem is in the ringed-module presentation and
also needs an identification with the fixed-scalar derived comparisons. The
missing bridge calculations are now explicit, independently takeable items.

The original claim that Step 5 requires a fully faithful J and an invertible unit
was stronger than necessary. An arbitrary adjunction suffices for restriction
injectivity on a source isomorphic to J(P), as the complete private proof shows.
No false statement or target-statement change was found.

Edge cases checked in the new statements: empty opens and zero objects introduce
no extra choices; identity geometric maps use the displayed actual unitors; zero
coefficient rings are permitted; odd shifts use both Koszul symmetries whose
product sign is +1. The unbounded case uses coproduct totalization, not products
or bounded resolutions. The identity equation holds for arbitrary f by naturality,
without the original unit-normalization or isomorphism hypothesis.

## New nodes

`lem-pur-supported-tensor-cartesian-unit` states only the restriction equation for
transport of an arbitrary unit-normalized arrow, combining original Steps 1, 3,
and 4. Its source is the original node's explicit beta-unit calculation and the
latest blueprint's symmetry paragraph, with Stacks 03S6/07A4/0GL1. It leaves
invertibility and all uniqueness conclusions to the complete parent proof.

`lem-pur-supported-tensor-signed-unit` is original Step 6 restricted to the signed
unit equation on a single open immersion. It assumes that equation for an
arbitrary arrow and proves it for its signed conjugate. The two symmetries,
comparison maps and units are the actual existing definitions. Its source is the
same signed symmetry calculation and Stacks 07A4/0GL1.

`lem-pur-supported-tensor-identity-unitor` isolates the actual identity-square
unitor calculation of Step 7. It is a naturality statement for arbitrary arrows,
with the identity-pullback unitors spelled out in its Lean type. It needs neither
a unit equation nor invertibility, and does not assert any Cartesian transport
or signed reversal away from the identity square. Its source is canonical
inverse-image identity coherence and the blueprint's identity clause.

Each node records LeanFinder, Loogle, LeanSearch and source grep searches. No
statement/definition repair or consumer adaptation was made, so no change record
is needed.

Blueprint search `tensor.*symmetr|supported.*tensor|tensor.*identity` returned
no matching blueprint node; the ancestor tool confirmed
`prop-pur-affine-space-composition-law` for all new nodes.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
