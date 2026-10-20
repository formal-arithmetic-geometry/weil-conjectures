## What changed

Proved `AlgebraicGeometry.Etale.arbitraryScheme_untensored_baseChange` without changing its signature. The proof first uses the source library's derived etale locality theorem on the pulled-back affine cover of Z. For affine charts it forgets prime-field module coefficients and applies the new, fully proved affine abelian theorem.

Added `Sheaf.AlgebraicGeometry.AbelianArbitrarySchemeUntensoredBaseChange`, containing the proved public theorem `abelian_affineScheme_untensored_baseChange` and proved private helpers. These construct the finitely generated subalgebra approximation, actual product-limit cones, the constant coefficient continuity data and its coherence, and the bounded-below cohomology argument. Finite-type base change and higher-direct-image continuity are the existing declared inputs. No definition or existing statement was repaired, and no consumer adaptation was needed. Both files compile together through lcompile.py --all, with no warnings.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.arbitraryScheme_untensored_baseChange`.
Added 0 holes. The new `AlgebraicGeometry.Etale.abelian_affineScheme_untensored_baseChange` is fully proved. There are zero `sorry`s in either delivered module, including every helper and definition. This is a proof, not an unfinished decomposition; the existing finite-type and continuity declarations are imported as required by the stage-3 brief.

## No longer needed

Removed direct imports from the assigned module:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.SixFunctors.BaseChange.Etale`
- `WeilConjectures.AlgebraicGeometry.DerivedExchangeTermwise`
- `Sheaf.Paper.KunBaseChange`
- `Sheaf.AlgebraicGeometry.StalkFaithfulDerived`
- `WeilConjectures.Mathlib.RingTheory.Adjoin.FG`
- `WeilConjectures.AlgebraicGeometry.LimitFibreProducts`
- `Sheaf.Targets.BaseChangeTowardsFields`
- `Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `Sheaf.Paper.KunBcMapOnCohomology`
- `Sheaf.AlgebraicGeometry.HigherDirectImagesLimits`

Some retained mathematical inputs moved to the affine module: `BaseChangeTowardsFields`, `UnboundedExchangeAgrees`, and `HigherDirectImagesLimits`; their nodes remain used transitively. Exact inverse image and cohomology APIs are already supplied by the source derived-functor library. The coefficient comparison remains a direct input.

The old explicit resolution/locality route is unnecessary: `lem-weil-pbc-etale-restriction-injectives`, `lem-weil-pbc-etale-underived-exchange-restriction`, `lem-weil-pbc-open-immersion-etale`, `lem-weil-pbc-derived-exchange-termwise`, `lem-weil-pbc-dplus-injective-representative`, `lem-kun-bc-base-change`, and `lem-kun-stalk-faithful-derived` are not imported for this proof. Source etale locality handles their combined purpose.

`lem-weil-pbc-limit-fibre-products` / `WeilConjectures.AlgebraicGeometry.LimitFibreProducts` is replaced by the direct universal-property proof in private helpers, together with `lem-weil-pbc-fibre-product-affine-transition`. `lem-kun-bc-map-on-cohomology` / `Sheaf.Paper.KunBcMapOnCohomology` and `lem-weil-pbc-unbounded-derived-iso-cohomology` are unnecessary: the continuity statement already uses the specified bounded-below homology maps, and the source derived-category API detects isomorphisms. The unbounded exchange definition is supplied through the exchange-agreement input, not imported separately. `lem-kun-algebra-union` and Spec-preserves-limits remain used through the source ring-colimit package and Mathlib. No globally unused module is asserted withdrawn; other consumers may still require these nodes.

Removed obsolete top-level tool-use approvals for inverse-image exactness, injective restriction, underived etale exchange, Spec/limit, product limits, unbounded cohomology detection and termwise derived exchange; their former direct roles are replaced as described above.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned sequence required considerable explicit continuity coherence for the constant coefficient system; the proof supplies it. The source library already has a proved module-coefficient derived etale-locality theorem, avoiding the longer resolution-level locality plan. The new affine statement was checked against empty Z, Z=Spec K, the zero coefficient sheaf, and infinitely generated coordinate algebras: its proof uses neither nonemptiness of Z nor finite type of B. The finite-subalgebra index is nonempty even for the zero algebra. All constructed limit data comes from universal properties, not an arbitrary witness of an unproved existence theorem.

## New nodes

`lem-kun-0f1j-abelian-arbitrary-scheme-untensored-base-change`: the affine abelian continuity part of the original node, now a fully proved theorem in its own module. Its affine hypothesis makes it strictly a part of the global argument; the global proof genuinely combines it with coefficient comparison and etale locality. No new unfinished item or change record is added.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
