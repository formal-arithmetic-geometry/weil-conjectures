## What changed

Replaced the sole sorry in `AlgebraicGeometry.IsCurve.prime_biproduct_invertible_iff`
with a proof preserving every binder and the conclusion. Added proof-only imports of
`Mathlib.Algebra.Category.Grp.Biproducts` and
`Sheaf.AlgebraicGeometry.Curve.PrimeAnnihilatedInvertibleCases`.

Private proved helpers construct the product equivalence for an additive functor,
prove finiteness and natural-transformation bijectivity componentwise, and specialize
bijectivity to étale cohomology pullback. The main proof splits on whether the common
prime is a unit. In the unit case all coefficient hypotheses hold; in the nonunit
case an assumed invertible-order hypothesis forces the individual sheaf to be zero.
Updated the item's node proof, proof_deps and proof_origin to follow this proof.
No public signature, definition, or unit realization was changed.

## Proved and sorry left

`AlgebraicGeometry.IsCurve.prime_biproduct_invertible_iff`
(node `lem-pbc-f1-prime-biproduct-invertible`) has a complete proof with no sorry.
No new sorry or new module is added. The existing dependency
`AlgebraicGeometry.Scheme.prime_annihilated_invertible_cases` is proved in its source.
The actual item module now compiles cleanly with the existing dependency available
in the refreshed compiled library (15 seconds, exit code 0). No dependency was
copied, restated, or rebuilt. The required `deliver3.py ... --no-push` dry run printed OK: the delivery
compiles and passes preflight, except for the second reading reserved for the
second reader. Nothing was pushed.

## No longer needed

The original public import of `WeilConjectures.AlgebraicGeometry.Curve.Assertions`
is retained for the statement. Removed the original proof-only imports:
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`,
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`. Constructibility is
already available from Assertions; stalk conservativity is used transitively by
the prime-annihilated cases lemma rather than directly here.
The proof does not need the module
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` or its node
`lem-weil-pbc-cohomology-pullback-functorial`: the source's already-proved
`Etale.cohomologyMap_map` provides exactly the naturality required, without
pullback composition, resolution comparison, or identity coherence.
No Ext-to-derived-global-sections bridge is needed.
The geometric-stalk-conservativity node is no longer a direct proof dependency:
its application is reused through the existing prime-annihilated cases lemma;
it remains a transitive dependency and is not globally pruned.
The constructibility-definition node is not used to construct a finite sum here:
the statement already supplies constructibility of H and each component.
Its notion still occurs in the signature and its statement dependency is retained.
No unit statement or realized step is bypassed (checked `dag/units/sk-thm-p1.json`).

## Where the brief, the DAG or earlier work was wrong

The original planned dependency on the bundled pullback-functoriality theorem is
unnecessary: only naturality is used, and the source library already proves it.
Earlier attempts were blocked by a missing compiled artifact for the existing
prime-annihilated cases module. The refreshed library now exposes that module,
and the unchanged preserved proof compiles. No mathematical statement error
was found. No dependency was copied, restated, or rebuilt to bypass the project's
green-build rule.


## Second reading by P2

1. Interface: PASS. Compared the delivered module with the repository by diff,
   then checked the existing theorem signature byte for byte. All binders and the
   conclusion are unchanged; no existing definition changes and no change record
   is needed. The sole public import remains Assertions; both added imports are
   proof-only. Only one Lean module and its existing node are delivered.
2. Proof: PASS. Independently compiled the module with lcompile.py: no errors or
   warnings (14.9 seconds). Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.IsCurve.prime_biproduct_invertible_iff`: precisely propext,
   Classical.choice and Quot.sound (16.1 seconds), with no sorryAx. Read every
   private helper and the main proof. No sorry or forbidden declaration occurs
   in the delivered module; sumEquiv is an explicit composition of equivalences,
   not a hollow definition.
3. Split statements: PASS, none added or left. The prime-annihilated cases lemma
   is an existing proved dependency, not a renamed restatement of this item.
   Checked empty and singleton index families, zero component groups, degree
   zero, and the nonunit-prime case. Empty products are singleton groups; zero
   supplies the supported vectors and preimages; the nonunit case uses the
   conditional invertible-order assumption to force each relevant sheaf zero.
4. Route and pruning: PASS. Searched lean/ for the componentwise equivalence,
   finite-sum helpers and naturality, and Mathlib function/biproduct infrastructure
   for product bijectivity and finiteness. No shorter existing public theorem
   closes the conditional C4/C6 assertion. Existing Mathlib product equivalences
   and source naturality are already reused. Both proof imports are needed for
   their named declarations. Every removed old proof dependency is covered under
   No longer needed: pullback-functoriality, direct stalk conservativity, and the
   constructibility-definition node. The latter remains a statement dependency;
   stalk conservativity remains transitive through the cases lemma. Read
   dag/units/sk-thm-p1.json realized: this item is below its preserved steps,
   and no unit statement or step is bypassed.
5. DAG: PASS. Compared the node diff: only proof, proof_deps and proof_origin
   change. The four steps match the generic finite-product identification,
   comparison naturality, unit case and zero-sheaf case in Lean. proof_deps is
   exactly the union of uses. No new nodes or statement changes occur.

Second-reading changes: corrected the theorem docstring to say that the given
constructibility hypotheses are installed, and to name the actual product
identification (Functor.mapBiproduct and AddCommGrpCat.biproductIsoPi). Kept the
proof and node records unchanged. Added this independent review and its checks.
