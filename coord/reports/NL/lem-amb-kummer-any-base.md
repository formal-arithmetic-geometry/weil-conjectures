## Worker report

Existing declaration: `AlgebraicGeometry.Scheme.kummerSequence_shortExact`, in
`WeilConjectures.AlgebraicGeometry.Sites.Kummer`, source lines 202–219
(the theorem starts at line 213). No module is written: this is exactly the node's
statement, already proved upstream. Only the item's `lean` record changes.
The source blueprint page
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-amb-kummer-any-base.md`
was read in full.

Hypothesis and clause correspondence:

- Arbitrary scheme T: the section binds `(X : Scheme.{u})`, with arbitrary universe u.
  There is no field, curve, finiteness, smoothness, or connectedness assumption.
- Integer n: the section binds `(n : ℕ)`, the exponent of the displayed power map.
- n invertible on T: `(hn : IsUnit (n : Γ(X, ⊤)))`. A global section is invertible
  exactly when it is locally invertible everywhere; its local inverses glue uniquely.
- The small etale sheaves: `X.kummerSequence n` has type
  `ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- μ_n: `rootsOfUnitySheaf X n = kernel (n • 𝟙 X.gmSheaf)`.
- The inclusion: `(X.kummerSequence n).f = kernel.ι (n • 𝟙 X.gmSheaf)`.
- Both copies of G_m: `X.gmSheaf`, whose sections are the units of the structure
  ring, written additively and universe-lifted (read in `Sites/Gm.lean`, lines 100–124).
- The map z ↦ z^n: `(X.kummerSequence n).g = n • 𝟙 X.gmSheaf`.
  Additive notation for the multiplicative group changes powers into n-fold sums.
- Exactness of the whole displayed sequence, including both outer 1 terms:
  `(X.kummerSequence n).ShortExact`. Mathlib's `ShortComplex.ShortExact` has fields
  `exact`, `mono_f`, and `epi_g`, giving middle exactness and both endpoint conditions.
- Same Kummer sequence as def-sc-kummer-sequence with the base replaced by T:
  this is literally its recorded `AlgebraicGeometry.Scheme.kummerSequence`, whose
  definition already takes an arbitrary scheme.

Dependencies read:

- `def-sc-kummer-sequence`: recorded declaration
  `AlgebraicGeometry.Scheme.kummerSequence`, module
  `WeilConjectures.AlgebraicGeometry.Sites.Kummer`. Its complete definition and
  docstring at lines 140–155 were read. The item intentionally uses this definition
  on any scheme, exactly as its own statement directs.
- `def-weil-pbc-etale-sheaves`: its record explicitly identifies Ab(T_et) as
  `CategoryTheory.Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}`. That is the
  category in the Kummer definition. The record also lists unrelated set-valued
  predicates, torsion, and module sheaves, none of which this item needs. The
  recorded module `WeilConjectures.AlgebraicGeometry.EtaleSheaves` is absent in
  both supplied trees; the available original module
  `lean/Sheaf/AlgebraicGeometry/EtaleSheaves.lean` was read in full. This does not
  obstruct reuse: the requisite Mathlib Sheaf category is available through Kummer,
  and no declaration from the missing module is needed or imported by this item.

Edge cases checked: n = 1 gives trivial kernel and the identity power map.
On the empty scheme all units form the trivial group, so the statement holds even
for n = 0 (which is invertible only in the zero global-section ring). The actual
source proof explicitly handles n = 0; its docstring's n ≥ 1 is not a binder.
On a nonempty scheme n = 0 cannot satisfy hn. In characteristic p the exponent p
fails the invertibility hypothesis. Disconnected and non-affine schemes remain
included; the sheaf epimorphism is local surjectivity, not surjectivity on global
sections. No statement correction or disputed statement is needed. Naturality is
mentioned in the node's proof, but is not an extra clause of its statement.

Searches (2026-10-15):

- msearch.py leanfinder: "The Kummer sequence of etale sheaves on any scheme is
  short exact when n is invertible" returned eight unrelated exact-sequence hits,
  no Mathlib Kummer theorem.
- msearch.py loogle: "AlgebraicGeometry.Scheme.kummerSequence_shortExact"
  returned zero hits / unknown identifier in its Mathlib index.
- msearch.py grep: "kummerSequence|Kummer" in AlgebraicGeometry returned zero hits.
- rg on the upstream WeilConjectures tree for `kummerSequence_shortExact` found
  the exact theorem in `AlgebraicGeometry/Sites/Kummer.lean`, line 213, and uses.
  Searching the node id there found no hits (its upstream docstring cites the older
  blueprint label lem-sc-kummer-exact).
- rg on `lean/Sheaf` found existing uses of this theorem in curve base-change
  modules, and no separate theorem for this node.
- rg on `dag/lean_names_upstream.json` confirms the declaration is indexed.

Validation: deliver2.py --no-push performs a real server #check of the existing
fully qualified declaration through scompile.py; no new Lean files require compilation.

## Second reading by NL

I independently read the item JSON, its entire cited blueprint source (order 1567),
both statement-dependency nodes, and the upstream Kummer and Gm declarations.
The source is a blueprint Markdown node, not a Stacks tag: there is no additional
ambient Stacks hypothesis to import. The statement has the following complete list
of objects, hypotheses, and conclusions.

1. An arbitrary scheme T: upstream `variable (X : Scheme.{u}) (n : ℕ)` supplies X,
   with `universe u`. Verdict: exact; no field, curve, smoothness, separation,
   Noetherian, connectedness, or finiteness condition is present.
2. A natural exponent n invertible on T: the same n binder and
   `(hn : IsUnit (n : Γ(X, ⊤)))`. Verdict: exact. Invertibility of this global
   section is equivalent to invertibility locally on T, since local inverses glue.
   X and n precede hn; there are no extra instance arguments.
3. Sheaves on the small etale site: `kummerSequence` takes values in
   `ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
   Verdict: the abelian etale-sheaf category of the dependency, not module sheaves
   or sheaves on the Zariski site.
4. The left object μ_n and its inclusion into G_m:
   `rootsOfUnitySheaf X n = kernel (n • 𝟙 X.gmSheaf)` and
   `(X.kummerSequence n).f = kernel.ι (n • 𝟙 X.gmSheaf)`.
   Verdict: exact; the kernel consists precisely of units with n-th power one.
5. The two G_m objects: X₂ and X₃ of `kummerSequence` are both `X.gmSheaf`.
   In `Sites/Gm.lean`, `etaleStructurePresheaf` takes U to Γ(U, O_U),
   `gmPresheaf` takes its units via `CommRingCat.unitsAddCommGrpULift`, and
   `gmSheaf` bundles that actual sheaf. Verdict: the required G_m, with only
   additive notation and a harmless universe lift, not a constant sheaf.
6. The displayed power map: `(X.kummerSequence n).g = n • 𝟙 X.gmSheaf`.
   Verdict: exactly z ↦ z^n under the additive presentation of units; the
   upstream `kummerSequence_g_app_apply` also records its action on sections.
7. Exactness at every term, including both outer trivial groups:
   `(X.kummerSequence n).ShortExact`. I read Mathlib's structure, whose fields
   are `exact`, `mono_f`, and `epi_g`. Verdict: all three clauses are present;
   the final epimorphism is sheaf local surjectivity, not global surjectivity.
8. The same sequence as def-sc-kummer-sequence on the new base: its recorded
   declaration is literally `AlgebraicGeometry.Scheme.kummerSequence` in
   `WeilConjectures.AlgebraicGeometry.Sites.Kummer`. I read its signature and
   construction at lines 140–155 and the dependency's blueprint source.
   Verdict: the declaration already accepts any scheme, as this node requires.

Dependency audit: def-weil-pbc-etale-sheaves has a mixed record; its explicit
Ab(T_et) component is Mathlib `Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}`.
The recorded `IsLocallyConstantEtaleSheafOfSets` predicate is not used as a
substitute for that category. I read the available Sheaf/AlgebraicGeometry/
EtaleSheaves module as well. The recorded upstream module is absent in this
checkout, but this theorem needs none of its extra predicates or declarations:
the actual category and site are already provided by the existing Kummer module.
No dependency repair or substitute object is needed.

Edge cases: n = 1 gives a trivial kernel and identity; no n > 0 assumption is
silently introduced. For n = 0, hn forces the global-section ring to be zero,
so T is empty and the sequence is trivial. The upstream local-surjectivity proof
explicitly splits off n = 0 and uses subsingleton rings there. Thus the docstring's
n ≥ 1 is not an extra hypothesis of the declaration. A positive-characteristic
scheme permits precisely the n whose local images are units; characteristic-
p divisibility is excluded where appropriate by hn. Empty schemes, disconnected
schemes, and non-affine schemes are included. There is no indexing set in the
statement; the site includes empty test schemes. Arbitrary scheme universe u
is covered, and AddCommGrpCat.{u+1} accommodates the lifted section groups.

Independent searches used wording different from the first reader:
- msearch leanfinder: "An invertible natural number gives a locally surjective
  power endomorphism of the sheaf of units on the small etale site" returned
  eight related local-surjectivity/etale hits, no exact Mathlib theorem.
- msearch loogle: `"rootsOfUnitySheaf"` returned zero hits.
- msearch grep over all Mathlib: `rootsOfUnitySheaf|kummerSequence|Kummer sequence`
  returned zero hits.
- rg over the complete upstream WeilConjectures tree found Kummer and
  roots-of-unity material, including exactly the recorded theorem in Sites/Kummer.
  rg over lean/Sheaf found curve base-change users of the same upstream theorem;
  dag/lean_names_upstream.json also indexes it. No duplicate module is warranted.

Mismatches and changes: none in the statement or record. The existing signature
in lean.statement is verbatim the theorem signature at lines 213–214; X, n, and
u are bound by the enclosing section. The upstream theorem has an actual proof,
not a hollow definition or an assumed exactness property. Its docstring explains
the kernel and the etale root-cover proof, under the older blueprint label
lem-sc-kummer-exact. Reusing it is the existing-declaration rule, not writing a
new stage-2 proof. The last sentence of the node's proof mentions naturality,
but its statement has no additional naturality conclusion. No new nodes,
dependency modules, or statement correction are part of this delivery.

Validation: the dry run and delivery check the existing fully qualified theorem
through scompile.py on the server; there are no delivered Lean files to compile.
