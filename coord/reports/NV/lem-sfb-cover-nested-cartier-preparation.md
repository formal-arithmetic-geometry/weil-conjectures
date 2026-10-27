## Worker report

The module `Sheaf.AlgebraicGeometry.CoverNestedCartierPreparation` states
`AlgebraicGeometry.exists_cover_nested_cartier_preparation`, with `sorry` as its entire
proof. Its docstring carries all nine proof steps of the current, reviewed Q134 split.
The item copy changes only `lean`; no statement correction, new node, or dependency repair
is needed. There is no statement dispute.

The auxiliary `Scheme.coverGenericResidueAlgebra` is an instance wrapper around
`Spec.homEquiv` applied to the chosen point morphism and the generic-fibre projection,
then `RingHom.toAlgebra`. It contains real data and no postponed proof. It installs the
canonical K-algebra on F, without choosing an embedding or defining another function
field, normalization, or Cartier predicate. Both declarations belong to this node and
are listed in `lean.declarations`.

### Hypotheses, one by one

- The field k is `{k : Type u} [Field k]`.
- The nonempty integral scheme T is `(T : Scheme.{u}) [IsIntegral T]`;
  Mathlib's integral class includes nonemptiness.
- Its k-structure is `t : T ⟶ Spec (.of k)`.
- Separatedness is `[IsSeparated t]`.
- Finite type over k is `[LocallyOfFiniteType t] [QuasiCompact t]`.
- The two open subschemes are `S Tcirc : T.Opens`, with their canonical open
  immersions and actual restriction structure sheaves.
- Nesting is `hST : S ≤ Tcirc`.
- Both density assumptions are `hS : Dense (S : Set T)` and
  `hTcirc : Dense (Tcirc : Set T)`.
- The nonempty source of the prescribed cover is `(H : Scheme.{u}) [Nonempty H]`.
- The cover itself is `c : H ⟶ S.toScheme` with `[IsFinite c] [Etale c] [Surjective c]`.
- The base function field K is precisely `T.functionField`, the generic stalk, as in
  the arbitrary integral-scheme clause of `def-sc-function-field`.
- The structure map implicit in the node's fibre product is named
  `η : Spec T.functionField ⟶ S.toScheme`. Its characterization
  `hη : η ≫ S.ι = T.fromSpecFunctionField` specifies the canonical generic-point lift.
  This introduces no additional mathematical restriction: a dense open of integral T
  contains the generic point, and the open immersion is a monomorphism, so this lift
  exists and is unique. Quantifying over a characterized lift avoids a private choice
  or an extra theorem with `sorry` just to build its data.
- The chosen point is `x : (pullback c η : Scheme.{u})`, exactly a point of H ×_S Spec K.
- F is literally `(pullback c η).residueField x`, not an unrelated extension. Its
  canonical K-algebra is the instance described above. The restriction to one common
  universe is the standard scheme-category convention; no bound on dimension, degree,
  characteristic, cardinality of components, or field perfection is imposed.

### Conclusions, clause by clause

In the following paragraph abbreviations are explanatory only; the Lean file uses the
full terms. Write F for the displayed residue field, X for `T.normalizationIn F`, and
q for `T.fromNormalizationIn F`.

- F/K finite is the first conjunct `FiniteDimensional T.functionField F`.
- X is exactly the existing normalization in F, not an arbitrary finite cover.
  Giving the claimed properties of this canonical construction supplies the node's
  existential X and q without a new normalization predicate.
- X integral is the explicit `IsIntegral (T.normalizationIn F)` conjunct. The existing
  integral-normalization instance also makes its function field well typed.
- Normality is stated pointwise as both `IsDomain (X.presheaf.stalk y)` and
  `IsIntegrallyClosed (X.presheaf.stalk y)` for every y, exactly the node's meaning.
- X separated finite type over k is `IsSeparated (q ≫ t)`,
  `LocallyOfFiniteType (q ≫ t)`, and `QuasiCompact (q ≫ t)`.
- The finite surjective map is `IsFinite q ∧ Surjective q`.
  The k-structure of X is q followed by t, so q is a k-morphism by construction.
- The function field identification k(X)=F is an isomorphism
  `eX : Spec F ≅ Spec X.functionField`, with
  `eX.hom ≫ X.fromSpecFunctionField = (T.fromSpecOfAlgebraFunctionField F).toNormalization`.
  For spectra of fields this is exactly a field isomorphism. The equation remembers
  the canonical map from Spec F to the normalization, so composing with q identifies
  the embeddings of K; an uncharacterized field isomorphism would be insufficient.
- B integral is `∃ (B : Scheme.{u}) (_ : IsIntegral B)`.
- The modifying morphism is `b : B ⟶ X`, with `IsProper b ∧ IsDominant b`.
- The k-structure of B is `(b ≫ q) ≫ t`. Its separatedness and finite type are the
  corresponding three explicit conjuncts. This also makes b a k-morphism.
- Birationality of b, including compatibility with K, is an isomorphism
  `eB : Spec X.functionField ≅ Spec B.functionField` satisfying
  `eB.hom ≫ B.fromSpecFunctionField ≫ b = X.fromSpecFunctionField`.
  Thus the isomorphism is the inverse of the function-field map induced by b.
  Composing eX and eB identifies k(B) with F over K, and composing the displayed
  equations with q gives the node's function-field assertion for g=qb. These are the
  same induced field identifications, not independent arbitrary isomorphisms.
- The isomorphism over q^{-1}S is `IsIso (b ∣_ (q ⁻¹ᵁ S))`.
- The first factorization through c is `∃ a : (q ⁻¹ᵁ S).toScheme ⟶ H,
  a ≫ c = q ∣_ S`.
- The two quasi-coherent ideals are `∃ I J : B.IdealSheafData`.
- Each is effective Cartier by `I.IsInvertible ∧ J.IsInvertible`. The recorded
  predicate defines this as affine-locally generated by a single nonzerodivisor;
  it does not merely assert invertibility of some abstract module.
- The first support equality is `(I.support : Set B) =
  (((b ≫ q) ⁻¹ᵁ S) : Set B)ᶜ`.
- The second support equality is `(J.support : Set B) =
  (((b ≫ q) ⁻¹ᵁ Tcirc) : Set B)ᶜ`.
- The composite g is the actual term `b ≫ q`, with both `IsProper (b ≫ q)` and
  `IsDominant (b ≫ q)` explicitly required.
- Its factorization through c is a separate last existential with
  `a ≫ c = (b ≫ q) ∣_ S`.
- No ideal is required to be proper, nonunit, or to have nonempty support, and b is
  not required to be nontrivial. Thus unit ideals and identity modifications are allowed.

### Dependency declarations used

I read the statement and record of every statement dependency. The declarations are:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (Mathlib match).
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` and `IsSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `.Separated`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `.QuasiCompact`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`; the two subschemes use `Scheme.Opens`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `def-sc-function-field`: `Scheme.functionField` for the integral-scheme clause,
  `Mathlib.AlgebraicGeometry.FunctionField`; imported through the recorded module
  `WeilConjectures.AlgebraicGeometry.FunctionField`. The component-product declaration
  is not the notion appropriate to this integral T.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-residue-field`: `Scheme.residueField` and `Scheme.fromSpecResidueField`,
  `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-fin-normalization-extension`: `Scheme.normalizationIn` and
  `Scheme.fromNormalizationIn`, `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`.
- `def-nagata-effective-cartier-ideal`: `Scheme.IdealSheafData.IsInvertible`,
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`.

Statement modules are public imports; the recorded proof-dependency modules that are
available are plain imports. Mathlib-only proof ingredients are already available
through the statement imports. No dependency is redefined. The nine-step theorem
docstring retains every proof-dependency citation and the empty-complement argument.

### Source reading and edge cases

Read the local Stacks source: morphisms.tex, definition-normalization-X-in-Y (035H),
lemma-characterize-normalization (035I), lemma-normalization-localization (035K),
lemma-ubiquity-nagata (035B); divisors.tex,
lemma-blowing-up-gives-effective-Cartier-divisor (02OS) and
lemma-blow-up-pullback-effective-Cartier (0809). The universal property permits a
factorization to H even if S is nonnormal. The Cartier total transform survives an
ordinary blowup without a flatness assumption.

Checked S=Tcirc, Tcirc=T, S=T, both empty boundaries, dimension-zero T, disconnected
finite étale H, and nonnormal S. None is excluded. If S=T the restriction condition
makes b an isomorphism; the boundary ideals can both be units. Disconnected H is
allowed because only one chosen generic-fibre point is used. Empty T is excluded by
integrality as in the node, and empty S cannot be dense in this T. No normality of S,
normality of H, separability of the ground field, or normality of B was added.

### Searches and validation

Ran the prescribed logged `msearch.py` commands for NV and this item:

- LeanFinder: “A finite etale cover of a dense open in an integral variety admits a
  finite normalization and a proper birational modification with two nested effective
  Cartier boundaries”. Eight hits, all normalization constructors or universal-property
  maps; no combined preparation theorem.
- LeanSearch: “Normalization in a generic residue field followed by two blowups makes
  both complements of nested dense opens effective Cartier divisors”. Eight hits,
  normalization constructors and universal-property equations; no full theorem.
- Loogle: `AlgebraicGeometry.Scheme.normalizationIn,
  AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`. Zero hits; the first identifier
  is unknown to Mathlib's search index because it is upstream project code.
- Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsProper`. Nine hits, finite
  morphisms are proper and related finiteness characterizations; none gives the item.
- Logged Mathlib grep: `nested.*[Cc]artier|[Cc]artier.*nested|coverNestedCartier`.
  Zero hits.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for the exact node ID and the same
  nested-Cartier patterns found no statement of this item. The Sheaf hits are unrelated
  localized intersection-theory flag products/comparisons.
- Read existing `normalizationIn`, `fromNormalizationIn`, the generic function field,
  `IsInvertible`, and the finite-normal-relative-curve and normalization-extends-cover
  statements to check interfaces and generic-field compatibility. These are ingredients
  or more specialized geometric results, not copies of this statement.

The sandbox-only type probe identified a coercion ambiguity in a point binder written
`x : pullback c η`: Lean tried the category of types. The final file explicitly gives
`(pullback c η : Scheme.{u})`. Every variable and universe is bound explicitly, with
`set_option autoImplicit false`; the delivered module contains no probes.

`scompile.py NV lem-sfb-cover-nested-cartier-preparation` compiled the delivered file
both in sandbox mode and under its final module name, cleanly, in about three seconds
per pass. There are no warnings or errors. This retry writes the actual stage-2 Lean
record; the previous attempt's unchanged stage-1-node packet is not reused.

### Dry-run tool failure after repair

Ran `deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` twice.
The first run also found a signature-format mismatch: the record had included the
terminal `:=`, while preflight expects the signature before that delimiter. Removed
that delimiter from `lean.statement`; the second run accepts the statement record and
reports exactly one remaining failure:

> (c) lean/Sheaf/AlgebraicGeometry/CoverNestedCartierPreparation.lean
> (lem-sfb-cover-nested-cartier-preparation): imports module(s) of route-pivot dropped
> nodes: Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
> (lem-per-integral-blowup-projective-geometry) (coord/route-pivot-dropped.txt)

This is a stale ownership refusal, not a dropped-route dependency in this delivery.
The item's reviewed proof explicitly depends on the ACTIVE node
`lem-sfb-integral-blowup-projective-geometry`. Its current `lean.module` is precisely
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry`, and its declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
Read the current server source with the prescribed `scompile.py --source` wrapper:
the module and theorem both carry the active sfb blueprint tag, and the current theorem
has the affine finite-generation hypothesis recorded in that active node. The old
`lem-per-integral-blowup-projective-geometry` record points at a different old declaration
(`integral_blowup_projectiveBundle`) and says its former module was deleted on 2026-10-20.
The path has since been reused by the active sfb dependency.

The compiler accepts the complete delivery including this import. The second dry run
recompiled it successfully and staged exactly the report, item node, and Lean module,
then failed only the stale route-pivot check. The preflight must distinguish the new
active owner from the obsolete perverse-node binding. No tool, dropped-node registry,
shared node, or library source was edited. Removing the required proof import or
copying its theorem under another path would work around the gate and violate the
statement-stage contract. Nothing was pushed; all completed work remains in the sandbox.

### Dispatcher retry verification (2026-10-22 09:46 UTC)

Retained the saved module and node record. The required first dry run
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` again
failed with exactly the same single route-pivot dropped-module refusal quoted
above; nothing was pushed. A comparison with the current shared item confirms
that only `lean` differs. Read the current server module again using
`scompile.py --source Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry`: its
module and declaration docstrings both identify the active
`lem-sfb-integral-blowup-projective-geometry`, and its declaration is
`isIntegral_blowup_and_isProjectiveBundle` with the affine finite-generation
hypothesis. The current active dependency record names this exact module and
declaration. Thus the obsolete `lem-per` ownership in the preflight refusal
remains a tool fault. Per the launcher-tool rule, no gate, registry, launcher
script, or required proof import was modified to bypass it.

### Dispatcher retry verification (2026-10-22 09:49 UTC)

Started with the required saved-packet dry run, without changing the Lean module or node. The wrapper compiled the one Lean file and staged the three packet files, then rejected the required `Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` import under `lem-per-integral-blowup-projective-geometry`, with the same single route-pivot diagnostic quoted above. Nothing was pushed.

Re-read current server source through `scompile.py --source Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry`: both docstrings name `lem-sfb-integral-blowup-projective-geometry`; its declaration is `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`. The active dependency node records this exact module and declaration. Compared the packet node with the current shared node: only `lean` differs. There is no item repair note. The obsolete per-node binding still says its module was deleted on 2026-10-20, whereas the active sfb node records the new module on 2026-10-22. The refusal therefore remains a preflight ownership fault. The user forbids editing or bypassing the gate; removing the proof dependency import would violate stages/2-statements.md §3(7). Retained all work and recorded the tool failure here.

### Dispatcher retry verification (2026-10-22 09:53 UTC)

Started with the prescribed saved-packet `deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push`. The wrapper checked the one Lean file on the server, staged the three packet files, and exited 1 with exactly the same single route-pivot dropped-module refusal quoted above. Nothing was pushed.

Re-read `Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` through `scompile.py --source`: both docstrings identify the active `lem-sfb-integral-blowup-projective-geometry`, and the theorem is `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`. The current active node records that same module and declaration; the old `lem-per` record retains the reused path with a note that its old module was deleted. The active node remains a proof dependency of this item. Compared saved and current item nodes: only `lean` differs; no repair note is present. This is a preflight ownership fault, with no authorized packet repair: removing the required import violates stages/2-statements.md §3(7), and modifying the gate, registry, or launcher is prohibited. Retained the module and node unchanged.

### Dispatcher retry verification (2026-10-22 09:56 UTC)

Started with the required saved-packet dry run. `deliver2.py NV
lem-sfb-cover-nested-cartier-preparation --no-push` checked the Lean file on the
server and staged the three packet files, then exited 1 with the same single
route-pivot refusal: the required
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` import is attributed
to the retired `lem-per-integral-blowup-projective-geometry`. Nothing was pushed.

Re-read current server source with `scompile.py --source`: both docstrings name
the active `lem-sfb-integral-blowup-projective-geometry`, whose recorded module
and `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`
declaration agree with the source. The item still lists this active node as a
proof dependency. The saved node differs from the current shared node only in
`lean`, and there is no repair note. No authorized packet repair resolves this
preflight ownership fault: the required import must remain under
`stages/2-statements.md` §3(7), and the launcher-tool rule prohibits modifying or
bypassing the gate. Retained the saved Lean module and node unchanged.

### Dispatcher retry verification (2026-10-22 09:59 UTC)

Inspected the saved report and started with the required saved-packet dry run,
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push`. The wrapper
checked the one Lean file on the server and staged the three packet files, then
exited 1 with exactly one preflight reason: the import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is rejected as belonging
to the route-pivot dropped `lem-per-integral-blowup-projective-geometry`. Nothing
was pushed.

Read the current server module using `scompile.py --source`: both docstrings name
the active `lem-sfb-integral-blowup-projective-geometry`, and its theorem is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`,
with the affine finite-generation hypothesis. The current active node records
that exact module and theorem, and remains a proof dependency of the item. The
retired per-node retains the same module path and a deletion note dated
2026-10-20. Compared the saved item node with the current shared node: only
`lean` differs; no repair note is present.

This remains a preflight ownership fault. No authorized packet repair resolves
it: stages/2-statements.md §3(7) requires the active proof dependency import, and
the launcher instructions prohibit editing or bypassing the gate. Retained the
Lean module and node unchanged, and updated only this sandbox report.

### Dispatcher retry verification (2026-10-22 10:01 UTC)

Inspected the retained report and ran the required saved-packet dry run first. `deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` checked the Lean file on the server, staged the three delivery files, and exited 1 with the same single route-pivot ownership refusal quoted above. Nothing was pushed.

Verified current server source through `scompile.py --source Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry`: both docstrings identify the active `lem-sfb-integral-blowup-projective-geometry`, and its theorem is `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`. The current active node records this exact module and declaration and remains an item proof dependency. The retired `lem-per` record retains the reused path with its deletion note. The saved item differs from the current shared node only in `lean`; no repair note exists. The remaining refusal is in preflight ownership, not in the statement or compiler. Removing the required proof import would violate stages/2-statements.md §3(7), and the launcher-tool instructions forbid modifying or bypassing the gate. Retained the module and node unchanged.

### Dispatcher retry verification (2026-10-22 10:03 UTC)

Read the retained report and ran the prescribed saved-packet dry run first.
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` compiled the
one Lean file on the server and staged the three packet files, then exited 1
with the sole preflight diagnostic (c): the required import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is attributed to the
route-pivot dropped `lem-per-integral-blowup-projective-geometry`. Nothing was pushed.

Verified the current server source through `scompile.py --source`: its module
and theorem docstrings identify the active
`lem-sfb-integral-blowup-projective-geometry`, and its declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The current active node records this module and declaration, and the item still
lists it as a proof dependency. The saved item differs from the current shared
node only in `lean`; no repair note exists. The obsolete per-node retains the
reused module path. This is the same preflight ownership fault, rather than a
compiler or packet defect. Removing the required proof import violates
`stages/2-statements.md` §3(7); modifying or bypassing the gate is forbidden by
the launcher-tool instructions. Retained the Lean module and node unchanged.

### Dispatcher retry verification (2026-10-22 10:06 UTC)

Inspected the saved report and ran the required saved-packet dry run first.
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` checked the
Lean file on the server and staged the three delivery files, then exited 1 with
one preflight diagnostic (c): the required import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is attributed to the
route-pivot dropped `lem-per-integral-blowup-projective-geometry`. Nothing was pushed.

Read the current server module with `scompile.py --source`: both docstrings name
the active `lem-sfb-integral-blowup-projective-geometry`, and the declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The active dependency record agrees, and the item still names it in proof_deps.
The retired per-node retains the reused path with its 2026-10-20 deletion note.
Compared the saved item to the current shared item: only lean differs; no item
repair note is present. The single remaining diagnostic is a preflight ownership
fault. Stages/2-statements.md section 3(7) requires this active proof import, and
the launcher-tool instructions prohibit modifying or bypassing the gate. Retained
the Lean module and node unchanged, recording the failure only in this report.

### Dispatcher retry verification (2026-10-22 10:10 UTC)

Inspected the retained report and ran the prescribed saved-packet dry run first.
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` checked the
Lean file on the server, waited for shared-fetch bookkeeping, staged exactly the
three packet files, then exited 1 with one preflight diagnostic (c): the import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is attributed to the
route-pivot dropped `lem-per-integral-blowup-projective-geometry`. Nothing was pushed.

Verified current server source through `scompile.py --source`: its module and
theorem docstrings identify the active `lem-sfb-integral-blowup-projective-geometry`,
and its declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The current active node records exactly this module and declaration and remains
an item proof dependency. The retired per-node retains the reused path with its
2026-10-20 deletion note. The saved item differs from the current shared item
only in `lean`; no repair note exists. This is a preflight ownership fault.
Removing the required proof import violates stages/2-statements.md section 3(7);
editing or bypassing the gate is forbidden by the launcher-tool instructions.
Retained the Lean module and node unchanged and recorded the diagnostic here.

### Dispatcher retry verification (2026-10-22 10:12 UTC)

Inspected the saved report and ran the required saved-packet dry run first:
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push`. The wrapper
checked the one Lean file on the server and staged the three packet files, then
exited 1 with the sole preflight diagnostic (c): the required import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is attributed to the
route-pivot dropped `lem-per-integral-blowup-projective-geometry`. Nothing was pushed.

Read current server source through `scompile.py --source`: its module and theorem
docstrings identify the active `lem-sfb-integral-blowup-projective-geometry`, and
the declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The active dependency record agrees and remains an item proof dependency. The
retired per-node retains the reused module path with its deletion note. The saved
item differs from the current shared item only in `lean`; no repair note exists.
This is a preflight ownership fault. Removing the required proof import violates
stages/2-statements.md section 3(7), and the launcher-tool instructions forbid
editing or bypassing the gate. Retained the module and node unchanged.

### Dispatcher retry verification (2026-10-22 10:14 UTC)

Inspected the retained report and started with the required saved-packet dry run.
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` checked the
Lean file on the server and staged the three packet files, then exited 1 with
one preflight reason:

```text
(c) lean/Sheaf/AlgebraicGeometry/CoverNestedCartierPreparation.lean
(lem-sfb-cover-nested-cartier-preparation): imports module(s) of route-pivot
dropped nodes: Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
(lem-per-integral-blowup-projective-geometry) (coord/route-pivot-dropped.txt)
```

Read current server source with `scompile.py --source
Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry`: both docstrings
identify the active `lem-sfb-integral-blowup-projective-geometry`, and the
declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The active dependency records this exact module and declaration and remains in
the item's proof dependencies. The retired per-node retains the reused module
path and its 2026-10-20 deletion note. Compared current and saved item JSON:
only `lean` differs; no item repair note exists.

This is a preflight ownership fault. Removing the required proof import would
violate stages/2-statements.md §3(7); editing or bypassing the gate or its
registry is prohibited by the launcher-tool instructions. Retained the saved
Lean module and node unchanged. Nothing was pushed.

### Dispatcher retry verification (2026-10-22 10:16 UTC)

Inspected the saved report and ran the prescribed saved-packet dry run first.
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` checked
the Lean file on the server and staged the three packet files, then exited 1
with the sole preflight diagnostic (c): the required import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is attributed to
the route-pivot dropped `lem-per-integral-blowup-projective-geometry`.
Nothing was pushed.

Read current server source using `scompile.py --source`: both docstrings
identify the active `lem-sfb-integral-blowup-projective-geometry`, and its
declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The current active node records this exact module and declaration, and remains
in the item's proof dependencies. The retired per-node retains the reused
module path with its 2026-10-20 deletion note. Compared the saved item with
the current shared item: only `lean` differs; no repair note exists.

This remains a preflight ownership fault. Removing the required proof import
violates stages/2-statements.md section 3(7); editing or bypassing the gate
is prohibited by the launcher-tool instructions. Retained the Lean module
and node unchanged.

### Dispatcher retry verification (2026-10-22 10:19 UTC)

Inspected the saved report and ran the required saved-packet dry run first:
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push`. The wrapper
checked the one Lean file on the server and staged the three packet files, then
exited 1 with the sole preflight diagnostic (c): the required import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is attributed to
retired `lem-per-integral-blowup-projective-geometry`. Nothing was pushed.

Read current server source using `scompile.py --source`: its module and theorem
docstrings identify active `lem-sfb-integral-blowup-projective-geometry`, with
declaration
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The active dependency record agrees and remains in the item's proof dependencies.
The retired per-node retains the reused path with its deletion note. The saved
item differs from the current shared item only in `lean`; no repair note exists.
The source and record therefore confirm a preflight ownership fault. Removing
the required proof import violates stages/2-statements.md section 3(7), and the
launcher-tool instructions prohibit editing or bypassing the gate. Retained
the module and node unchanged.

### Dispatcher retry verification (2026-10-22 10:22 UTC)

Read the retained report and ran the required saved-packet dry run first.
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` checked the
one Lean file on the server and staged the three packet files, then exited 1
with the sole preflight diagnostic (c): the required import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is attributed to
route-pivot dropped `lem-per-integral-blowup-projective-geometry`. Nothing was pushed.

Read the current server source using `scompile.py --source`: both docstrings
identify active `lem-sfb-integral-blowup-projective-geometry`, and the theorem is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The active node records exactly that module and declaration and remains in the
item's proof dependencies. The retired per-node retains the reused path and
its deletion note. The saved item differs from the current shared item only
in `lean`; no repair note exists. This confirms a preflight ownership fault.
Stages/2-statements.md section 3(7) requires this proof import; the launcher-tool
instructions prohibit editing or bypassing the gate. Retained the Lean module
and node unchanged.

### Dispatcher retry verification (2026-10-22 10:24 UTC)

Inspected the retained report and ran the mandatory saved-packet dry run first:
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push`. It checked
the one Lean file on the server, staged the three packet files, and exited 1
with the same sole preflight diagnostic (c): the required import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is attributed to
route-pivot dropped `lem-per-integral-blowup-projective-geometry`. Nothing was pushed.

Verified current server source with `scompile.py --source`: the module and
theorem docstrings identify active `lem-sfb-integral-blowup-projective-geometry`,
and the declaration is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The active dependency's record names exactly that module and declaration, and
it remains in the item's proof dependencies. The retired per-node retains
the reused module path with its 2026-10-20 deletion note. The saved item still
differs from the current shared item only in `lean`; no repair note exists.

This is the same concrete preflight ownership fault, with no packet repair
indicated by the diagnostic. Removing the import violates
`stages/2-statements.md` section 3(7); modifying or bypassing the gate is
prohibited by the launcher-tool instructions. Retained the module and node
unchanged and recorded this failed retry in the sandbox report only.

### Dispatcher retry verification (2026-10-22 10:26 UTC)

Inspected the retained report and ran the required saved-packet dry run first.
Repeated the dry run to retain its complete diagnostic. Both prescribed
`deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push` runs
checked the Lean file on the server and failed preflight with the same sole
reason (c): `Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is
attributed to dropped `lem-per-integral-blowup-projective-geometry`.
Nothing was pushed.

Verified current server source with `scompile.py --source`: both docstrings
identify active `lem-sfb-integral-blowup-projective-geometry`, and its theorem
is `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The active node records this module and declaration; the item still lists
that active node in proof_deps. The retired per-node retains the reused module
path and deletion note. The dropped registry names the per-node, not the
active sfb-node. The saved item differs from the current shared item only in
`lean`; there is no item repair note.

This is a concrete preflight ownership fault. Removing the required active
proof import would violate stages/2-statements.md section 3(7); changing or
bypassing the gate is prohibited by the launcher's instructions. Retained
the Lean module and node unchanged.

### Dispatcher retry verification (2026-10-22 10:28 UTC)

Inspected the retained report and ran the prescribed saved-packet dry run.
Repeated it to capture the complete diagnostic. The server compilation passed;
preflight exited 1 with exactly one reason (c): the required import
`Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry` is attributed to dropped
`lem-per-integral-blowup-projective-geometry`. Nothing was pushed.

Verified the current server source with `scompile.py --source`: its module and
theorem docstrings identify active `lem-sfb-integral-blowup-projective-geometry`,
and its theorem is
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_blowup_and_isProjectiveBundle`.
The active node records that exact module and declaration and remains an item
proof dependency. The retired per-node retains the same path with a deletion
note; only that retired id occurs in the dropped-node registry. The saved item
still differs from the current shared item only in `lean`; no item repair note
is present.

This is a preflight ownership fault with no packet repair indicated. Removing
the required import violates stages/2-statements.md section 3(7); editing or
bypassing the gate is prohibited by the launcher-tool instructions. Retained
the module and node unchanged.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
