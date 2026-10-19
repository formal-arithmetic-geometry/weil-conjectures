## What changed

Proved `WeilConjectures.integral_residue_tor` with its existing signature unchanged.
Represent each finite reduction by a cochain complex, choose a K-flat resolution,
transport constructibility along the representative isomorphism, and apply the
existing pro-etale residue Tor test. The residue comparison proved in the companion
module transfers the assumed interval to that test. The common interval in integral
constructibility then gives integral finite-Tor membership. The reverse inclusion is
definitional; extensionality gives equality of the predicates.

Added the proved companion theorem
`WeilConjectures.integralReduction_residue_homology_zero_iff` in
`Sheaf.Paper.IntegralReductionResidueHomology`. Uniqueness of universal left derived
functors identifies the recorded reduction functors with the existing normalized
coefficient-extension presentations. Their composition comparison and the inverse-limit
cone equations compare successive reduction with first reduction. The quotient-of-quotient
ring equivalence identifies the residue quotient with the first coefficient ring.
Tensor cancellation and the single-complex tensor comparison compute the chosen
K-flat model. Exact faithful restriction detects zero homology.

Every auxiliary construction is explicit or determined by the stated universal property.
There are no definition or statement repairs, no changed existing signatures, and no
consumer adaptations. The DAG records both actual proofs. All new proof imports are
private. The companion keeps only the two public imports needed by its statement.

Validation: both delivery modules compile together through `lcompile.py --all`.
The complete new comparison was also compiled during development. All scratch files
are outside the delivery's `lean/` directory.

## Proved and sorry left

Original holes: 1, `WeilConjectures.integral_residue_tor`.
Closed: 1, `WeilConjectures.integral_residue_tor`.
Added holes: 0. Remaining holes in both delivered modules: 0.
The new theorem `WeilConjectures.integralReduction_residue_homology_zero_iff`, node
`lem-coef-integral-residue-tor-residue-amplitude`, is proved as well.
No obligation is split off with `sorry`. Existing stated dependencies, including
successive derived quotient normalization, remain available obligations of the project;
this delivery proves its declarations from them as required by stage 3.

Edge cases checked: index n=0 gives the identity finite-to-first quotient map;
the projection compatibility proof includes that base case. The quotient-of-quotient
map is checked on all quotient representatives. Zero complexes and empty schemes
need no extra hypotheses. The coefficient comparison uses no boundedness,
constructibility, derived completeness or invertibility hypothesis.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.FiniteTorAmplitudeSites`

The first five are unnecessary direct imports of the parent after the coefficient
comparison is supplied by the proved companion. Their underlying tensor and universal
coefficient-extension theory remains used where needed through the companion's imports;
no global deletion of those modules is claimed. The site bridge is unnecessary because
the predicates and residue criterion already use the same pro-etale presentation.
The parent no longer directly uses `def-pc-kflat-complex`,
`def-pur-sheaf-tensor-product` or `lem-pur-derived-change-of-rings` as proof dependencies.

The companion's completed proof does not need `lem-pc-kflat-resolution` or
`lem-pur-kflat-change-of-rings`: its given resolution suffices for the finite tensor
computation, while the existing normalization theorem supplies composition. These two
entries were removed from its draft proof dependencies. The parent still needs K-flat
resolution existence. All original parent public imports are preserved. No unit route
is bypassed; the relevant unit's `realized` lists are empty.

## Where the brief, the DAG or earlier work was wrong

The inherited draft described an absent declaration named
`residue_tor_amplitude_of_integral_reduction`. Its node and report now name the actual
homology comparison in its companion module. The retained intermediate `sorry` has
been proved in this session; it is not delivered as a decomposition.

The previous claim that the universe-polymorphic coefficient interfaces were unusable
was too strong. Explicit coefficient universes and standard derived-category instances
make the computation and normalized-composition route work. An inherited private helper
also called a composition comparison where a natural-isomorphism comparison was needed;
the proof now constructs the latter from its homotopy natural transformations.

The blueprint's ordinary residue-test citation has the wrong site for these predicates.
The existing node's correction to the pro-etale residue test is retained. The mathematical
route remains the blueprint's coefficient associativity followed by the residue criterion.

## New nodes

`lem-coef-integral-residue-tor-residue-amplitude` records the proved theorem
`WeilConjectures.integralReduction_residue_homology_zero_iff` in
`Sheaf.Paper.IntegralReductionResidueHomology`. Despite its retained draft identifier,
it states only the coefficient comparison of zero cohomology in each degree, with no
constructibility or Tor-amplitude conclusion. Its statement is unchanged from the
retained sandbox, and its proof steps and dependencies now follow the complete Lean proof.
No new node has a `sorry`. No change record is needed because existing definitions and
statements are unchanged.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
