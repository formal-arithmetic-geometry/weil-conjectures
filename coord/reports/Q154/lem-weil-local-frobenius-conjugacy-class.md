## Worker report

The module `Sheaf.Paper.LocalFrobeniusConjugacyClass` states
`WeilConjectures.localFrobeniusConjugacyClass`. It uses the existing local Frobenius
construction from `WeilConjectures.localClosedFrobeniusCohomology`: the finite datum,
coefficient extension, finite-type model, Weil complex, closed point, two compatible
residue-field maps, and an arbitrary integer cohomological degree are explicit
arguments. The conclusion is an isomorphism between the two coefficient cohomology
modules whose composition with the second local Frobenius equals the first local
Frobenius followed by that isomorphism.

The hypotheses render as follows. `D : FiniteFieldDatum` is the finite-field datum;
`c : D.CoefficientDatum` and `E : Padic.FiniteCoefficientFields c.l c.Qbar` are the
coefficient data; `Y₀` is an object of `Over (Spec (.of D.k₀))` with
`LocallyOfFiniteType` and `QuasiCompact` structure-morphism instances; `K` is the
corresponding `sfWeilComplex`; `y` is a closed point; `ι` and `ι'` are ring maps from
its residue field to `D.k`; `hι` and `hι'` state compatibility with the `k₀`-structure;
`j : ℤ` is unrestricted. The two objects in the conclusion are the values of
`DerivedCategory.coefficientFdCohomology E.val j` on the point complexes at
`localClosedPoint D Y₀ y ι hι` and `localClosedPoint D Y₀ y ι' hι'`. The displayed
intertwining equation uses `localClosedFrobeniusCohomology` at those same points.

Dependency declaration used: `WeilConjectures.localClosedFrobeniusCohomology` from
`Sheaf.Paper.LocalFrobeniusTrace`. The proof is intentionally `sorry` at stage 2.
Edge cases checked include `ι = ι'` (identity conjugacy), residue degree `1`, orbit
length `2`, `j` in negative degrees, and zero cohomology modules; no hypothesis excludes
any of these.

Searches for an existing declaration found no matching Weil-sheaf stalk-conjugacy result.
LeanSearch / leanfinder queries for conjugacy of local Frobenius stalk operators returned
only finite-field ring-action Frobenius results (`isConj_arithFrobAt` and related
lemmas), which do not mention Weil complexes or stalks. Loogle query `"Frobenius",
"stalk"` returned no match. Grep of Mathlib for `localFrobenius|local_frobenius|stalk.*Frobenius`
and grep of `lean/Sheaf` found no declaration on the recorded fixed-pair categories.
The independent maintainer search did find upstream
`AlgebraicGeometry.WeilComplex.nonempty_equiv_stalkAtGeometricFiberPoint` in
`WeilConjectures/WeilSheaf/LocalFrobenius.lean:128`, as well as its Weil-sheaf
analogue at line 86. These are near matches, not declarations of the present node:
they use `PadicAlgCl l` coefficients and upstream `AlgebraicGeometry.WeilComplex`,
the bounded constructible subcategory of the derived category of Weil sheaves
(`WeilSheaf/Category.lean:157–178`). This node instead uses a fixed pair in the
rationalized constructible category over the finite field extension `E`, as
specified by `def-weil-weil-sheaf-complex` and implemented by `sfWeilComplex`.
No equivalence identifying these different categories and their local operators is
supplied by that upstream theorem. Its blueprint tag alone is not an exact match.
The earlier claim that source grep found no related declaration was incorrect.

## Second reading by Q154

I reread the node and module line by line. The finite-field datum, prime inequality
(encoded by `c.different`), coefficient extension, finite-type and quasi-compact
hypotheses, Weil complex, closed point, two residue-field maps, compatibility equations,
and arbitrary integer `j` all appear explicitly. The two stalk cohomology objects are
formed with the node's local closed-point construction, and the equation has exactly the
node's direction: the isomorphism carries the first local operator to the second. No
separatedness, finiteness, positivity, or equality of embeddings is added. The only
translation is that the node's “two `k₀`-embeddings” are represented by ring maps `ι`
and `ι'` together with the two explicit compatibility equations already required to
make geometric points of the base change.


Independent maintainer supplement (2026-10-18): the source search account above was
corrected after reading both upstream near-match signatures and their category
definitions. The Lean theorem and all mathematical node fields are unchanged.
The replacement lean record stores the exact multiline signature from the delivered
file; the original record already agreed after the delivery tool's whitespace
normalization. No extra dependency, helper, or statement correction is required.

Per-file compiler reproduction by the independent maintainer:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q154
lem-weil-local-frobenius-conjugacy-class
snapshot/lean/Sheaf/Paper/LocalFrobeniusConjugacyClass.lean` (one command).
Exit code 0. Output:

```text
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-3t2xbs4x/.lbuild) [155.2 s]
library Sheaf/Paper/LocalFrobeniusConjugacyClass.lean

[28.9 s]
```

The installed wrapper announces server execution and uses its server side overlay;
it is not the older local lcompile.py wrapper described in the brief. Both checks
used the immutable delivered file (SHA-256
`bf0affdfd76fda36fabd198d3458d58e99a51b3c95069d91f1b052832064b805`).
There were no diagnostic lines in the returned output. The wrapper announces a
60-second Lean limit after slot acquisition; its reported wall times include
waiting/overlay work. No global build or direct SSH command was run.
