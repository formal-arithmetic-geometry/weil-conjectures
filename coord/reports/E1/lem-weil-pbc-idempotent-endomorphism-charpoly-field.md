# Delivery report

Split the idempotent endomorphism characteristic-polynomial statement. The proof uses the existing image/base-change decomposition node, the existing basis-invariance and finite-free direct-sum characteristic-polynomial leaf, and three new Mathlib leaves created for this item: rank-nullity, the identity characteristic polynomial, and the zero characteristic polynomial. The adapted basis gives the factors `(T - 1)^r` and `T^(n-r)`; the final divisibility is elementary. No Lean was written or compiled.

The source is More on Algebra, Lemma Tag 07M5, line 2020. The source states the fibre formula without proof; the report's proof writes out the complementary image/kernel decomposition, dimensions, adapted basis, and polynomial divisibility.

## Review by E1

I checked the four proof steps against More on Algebra Tag 07M5 and the cited public decomposition and characteristic-polynomial nodes. The image and kernel of an idempotent give complementary subspaces; rank-nullity supplies the exponents, the adapted basis gives the factors for the identity and zero restrictions, and the divisibility conclusion is elementary. The three Mathlib leaves are statement-only, publicly named, and attributed to this item with independent searches. The parent metadata is corrected, the split report is complete, and no Lean was written.
