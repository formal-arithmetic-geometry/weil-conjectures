## Worker report

Stage 2, group NL, item `lem-exc-weakly-etale-excellent`.
The new module `Sheaf.RingTheory.ExcellentOfWeaklyEtale` states
`RingHom.isExcellent_of_weaklyEtale`. Its sole proof is `by sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The item's node copy changes only `lean`; the reviewed stage-1 split is preserved.
The previous attempt's refusal concerning a node already split and reviewed is not a
reason to resplit it: this delivery only supplies its missing Lean statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative rings R and S are `{R : Type u} {S : Type v}` with
  `[CommRing R] [CommRing S]`. Universes `u v` are explicitly bound and independent.
- The specified ring homomorphism is `(f : R →+* S)`; there is no unrelated algebra
  structure or replacement map.
- R excellent is `(hR : IsExcellent R)`, using precisely the recorded
  `def-exc-excellent-ring` declaration. Its unfolding includes Noetherianity, the
  G-ring condition, the J-2 condition, and universal catenarity. In particular,
  the paper's standing Noetherian hypothesis on the source is already present.
- S Noetherian is `[IsNoetherianRing S]`, the Mathlib predicate recorded for
  `def-weil-pbc-noetherian-ring`; this is equivalent to every ideal being finitely
  generated (`isNoetherianRing_iff_ideal_fg`).
- f weakly etale is `(hf : f.WeaklyEtale)`. The upstream `RingHom.WeaklyEtale`
  is definitionally `Algebra.WeaklyEtale R S` for exactly `f.toAlgebra`. This is
  the recorded weak-etale clause of `def-weil-pbc-ind-etale-algebra`, exposed by
  its module's public imports, rather than an ind-etale or finite-presentation
  assumption. Its `flat` field is `Module.Flat R S`, exactly flatness along f;
  its `flat_lmul'` field is `RingHom.Flat` of
  `(Algebra.TensorProduct.lmul' R (S := S)).toRingHom`, the map sending
  `s ⊗ t` to `s*t`. Thus both flatness clauses in the node are included.
  `RingHom.Flat` is the recorded predicate of `def-weil-pbc-flat-ring-map`.
- The sole conclusion S excellent is exactly `IsExcellent S`.
  No faithful-flatness, finite-type, finite-presentation, injectivity, domain,
  nonzero-ring, or local-ring assumption is added.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`, `IsExcellent` (with its definitions
  `IsQuasiExcellent` and `IsUniversallyCatenary`): read the whole local module,
  and confirmed the current source with `scompile.py --source`.
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`: read its signature,
  docstring and `isNoetherianRing_iff_ideal_fg`.
- `Sheaf.RingTheory.IndPrincipalZariski`, the recorded public interface exposing
  `Algebra.WeaklyEtale`; read the module and the original class in
  `Mathlib.RingTheory.Etale.Weakly`. Its upstream ring-map wrapper
  `RingHom.WeaklyEtale` is read in
  `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`. The wrapper fixes the algebra
  structure to `f.toAlgebra` and adds no mathematical condition.
- `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat` and
  `RingHom.flat_algebraMap_iff`: read their definitions and signatures.
- The already stated proof dependencies `Sheaf.RingTheory.QuasiExcellentNagata`
  (`isNagataRing_of_isQuasiExcellent`) and
  `Sheaf.RingTheory.NagataLocalization` (`isNagataRing_localization`) are ordinary,
  non-public imports. The latter's current source was read with `scompile.py --source`.
  The three Greco ascent lemmas in `proof_deps` have no Lean records yet, so there
  are no modules to import for them. They are not required to type this statement;
  their node ids and all their proof steps are retained in its theorem docstring.

Edge cases checked against the predicates and source:

- The target may be the zero ring: no Nontrivial or prime-existence hypothesis is
  present. Its prime-local conditions are vacuous, and excellence includes its
  Noetherian condition. This case is permitted by the signature.
- A zero source with a unital map forces the target to be zero; the theorem does
  not exclude this case. Identity maps and isomorphisms are also admitted.
- Localizations and strictly henselian localizations are not assumed to be of
  finite presentation. The weakly-etale predicate retains them whenever the
  target is Noetherian; it is not replaced by Etale or IndEtale.
- No characteristic or equality of source and target universes is imposed.
- S Noetherian is material: it is retained explicitly, not inferred from weak
  etaleness or silently omitted. R Noetherian follows from excellence.

Source check:

Read the official Cambridge PDF of Silvio Greco, Two theorems on excellent rings,
Nagoya Mathematical Journal 60 (1976), 139–149, DOI 10.1017/S0027763000017190.
The Foreword (printed p. 139) imposes commutativity and Noetherianity throughout.
Remark 5.2 (p. 146) identifies absolute flatness with flatness over A and over
B tensor_A B. Theorem 5.3(iv) (pp. 146–147) is precisely the claimed ascent of
excellence; its opening proof sentence assembles (i), (ii), and (iii), as does
this node's six-step proof. The PDF and its extracted text are kept only under
this item's `scratchpad/`, not in the shared literature directory or delivery.
Retrieval URL:
https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8F98780AD8CD9051866A2716C67833C3/S0027763000017190a.pdf/two-theorems-on-excellent-rings1.pdf
SHA256: `7e5b69f052d7966551e1fd292ed0916a7da9edeb70cd542b33d4052819ae074e`.

Searches made on 2026-10-16 (all through prescribed tooling or read-only rg):

- `msearch.py leanfinder`, query “A weakly etale homomorphism from an excellent
  ring to a Noetherian ring has excellent target”: eight hits about etaleness
  (including `Algebra.IsEtaleAt.comp`, `RingHom.Etale.toAlgebra`,
  `Algebra.Etale.comp`); no excellence ascent statement.
- `msearch.py loogle`, query `"WeaklyEtale"`: twelve hits about scheme weak
  etaleness and stability properties, no excellence statement.
- `msearch.py grep`, query `IsExcellent|[Ee]xcellence|[Ee]xcellent`: only an
  unrelated bibliographic adjective in `Mathlib/Algebra/Lie/InvariantForm.lean`.
- `msearch.py leansearch`, query “A weakly etale Noetherian algebra over an
  excellent ring is excellent”: service unavailable (Internal Server Error);
  no verdict inferred from that unavailable service.
- `rg` for `IsExcellent|[Ee]xcellent|[Ee]xcellence` in the upstream
  `WeilConjectures/` and side `lean/Sheaf/` trees: upstream only an unrelated
  cohomology comment; side tree has the excellent-ring definitions and
  quasi-excellent/Nagata theorem, but no weakly-etale excellence theorem.
- `rg` for the exact blueprint id in upstream: no result.
- `rg` for `RingHom.isExcellent_of_weaklyEtale|theorem isExcellent_of_weaklyEtale`
  in `dag/lean_names_upstream.json`, upstream, Mathlib, and side Lean: no result.
- Read the upstream `RingHom.WeaklyEtale` and Mathlib `Algebra.WeaklyEtale`
  signatures and bodies to verify the reused notion rather than defining a copy.

Validation: the prescribed `scompile.py NL lem-exc-weakly-etale-excellent`
compiled the delivered module successfully in both sandbox and library placements,
with no errors or warnings. The dry-run delivery check is run after this report.
No STATEMENT-DISPUTED flag or mathematical node fault was found.

## Second reading by NL

I independently read the item node, its six proof steps, every statement-dependency
node and its declaration source, the sandbox Lean file, and the Greco text retained
in `scratchpad/greco.txt`. No statement correction is present or needed. There are
no new nodes or dependency modules in this delivery.

The source comparison comes first: Greco's Foreword (printed p. 139) assumes all
rings commutative and Noetherian. Remark 5.2 (p. 146) identifies AF with flatness
over the base and over the tensor square. Theorem 5.3(iv) (pp. 146–147) then gives
excellence of the target from excellence of the source. Faithful flatness occurs
in parts (v) and (vi), the converse assertions, and is absent from part (iv).
I read these passages directly, including the opening proof sentence assembling
(i), (ii), and (iii). I also opened the official Stacks definitions
[092B](https://stacks.math.columbia.edu/tag/092B) and
[07QT](https://stacks.math.columbia.edu/tag/07QT); both agree with the notions used.
The shared checkout does not contain the Stacks .tex files at the recorded paths;
the published definitions supply the same source check without modifying it.

Item-by-item statement checklist and verdict:

1. Objects: arbitrary commutative rings R and S. Lean binds
   `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`; PASS. Both universes
   are declared by `universe u v` and may differ. Neither ring is required to be
   a field, domain, local, nonzero, or finitely generated.
2. Specified map: a unital ring homomorphism f from R to S. Lean has
   `(f : R →+* S)`; PASS. There is no independent algebra structure that could
   describe a different map.
3. Hypothesis: R excellent. Lean has `(hR : IsExcellent R)`; PASS. I opened
   `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` is the conjunction of
   `IsQuasiExcellent` and `IsUniversallyCatenary`. The former contains
   `IsNoetherianRing R`, `IsGRing R`, and openness of the regular locus for every
   finite type algebra; the latter contains the universal catenarity condition.
   This is the declaration recorded by `def-exc-excellent-ring`. Thus source
   Noetherianity is included, not a missing standing hypothesis.
4. Hypothesis: S Noetherian. Lean has `[IsNoetherianRing S]`; PASS. I read the
   Mathlib definition and `isNoetherianRing_iff_ideal_fg`: this is exactly finite
   generation of every ideal, as `def-weil-pbc-noetherian-ring` requires. An
   instance binder imposes the same mathematical hypothesis as an explicit proof.
5. Hypothesis: f weakly etale, with its two flatness clauses. Lean has
   `(hf : f.WeaklyEtale)`; PASS. I opened upstream
   `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`: `RingHom.WeaklyEtale f`
   installs precisely `f.toAlgebra`, then uses `Algebra.WeaklyEtale R S`.
   I opened Mathlib's `RingTheory/Etale/Weakly.lean`: its fields are
   `Module.Flat R S` and flatness of `Algebra.TensorProduct.lmul' R (S := S)`.
   The latter is multiplication from S tensor_R S to S. I also read
   `RingHom.Flat` and `RingHom.flat_algebraMap_iff`, which identify the first
   field with flatness of the specified f. These are the two notions recorded
   by `def-weil-pbc-ind-etale-algebra` and `def-weil-pbc-flat-ring-map`.
   `Sheaf.RingTheory.IndPrincipalZariski` publicly exposes the reused predicates;
   its principal ind-Zariski definition is not imposed in this theorem.
6. Sole conclusion: S excellent. Lean concludes `IsExcellent S`; PASS. No clause
   is dropped or added, and no existential object or reordered quantifier changes
   the assertion. Reading the fully explicit signature, all objects, instances,
   and hypotheses precede this conclusion exactly as in the node.

Dependency and proof audit: I read `Sheaf.RingTheory.GRing` to check that the
G-ring clause uses the canonical prime-local completion maps. I read the recorded
`isNagataRing_of_isQuasiExcellent` signature and its docstring in
`Sheaf.RingTheory.QuasiExcellentNagata`. I obtained and read the current
`Sheaf.RingTheory.NagataLocalization` source through `scompile.py --source`:
its signature includes the needed Nagata conclusion at every prime localization.
Both are ordinary proof imports. The three Greco ascent nodes have no recorded
Lean declaration; their absence as imports is appropriate and they remain named
in the proof docstring. That docstring follows all six node steps: unpack
excellence, obtain global and local Nagata hypotheses, apply the G-ring ascent,
retain J-2 from Nagata/J-2 ascent, retain universal catenarity from the third
ascent, and reassemble excellence. Both module and theorem docstrings name the
source and `(blueprint: lem-exc-weakly-etale-excellent)`.

Edge cases: the zero target ring is admitted, and a unital map out of the zero
source forces the zero target; neither is excluded by `Nontrivial`. Identity
maps, isomorphisms, and Noetherian localizations are admitted. There is no
characteristic restriction and no finite-presentation or faithful-flatness
hypothesis. Empty schemes correspond to the zero ring; no scheme or index set
is quantified in this ring statement, and no numerical parameter occurs.
The finite-type test algebras in excellence share their ring's universe (the
recorded dependency's interface); this is sufficient because a finite-type
algebra is a quotient of a finite-variable polynomial algebra and has a model
in that universe. The theorem itself does not equate source and target universes.

Independent searches on 2026-10-16, using other phrasings:

- `msearch.py leanfinder`: “An absolutely flat homomorphism of Noetherian rings
  preserves excellence”; eight hits about smooth flatness, going down, flat
  completion, and ring-map flatness. I read the returned types; none concludes
  excellence.
- `msearch.py loogle`: `"IsExcellent"`; zero hits.
- `msearch.py leansearch`: “Absolute flatness of a Noetherian algebra preserves
  excellent rings”; service unavailable (Internal Server Error). No absence
  conclusion is based on that failed service.
- Independent `rg -i` searches for `excellent|excellence|absolutely.?flat` in
  Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf`: Mathlib has weak
  etaleness and an unrelated bibliographic adjective; upstream has weakly etale
  and absolutely flat ring results but no excellence assertion. Side modules
  give the excellent-ring definition, quasi-excellent-implies-Nagata, and a
  specialized strict-henselization consumer; none states this general ascent
  theorem. A second side search for `IsExcellent|[Ee]xcellence|[Ee]xcellent`
  confirmed this. Searching upstream and `dag/lean_names_upstream.json` for the
  exact declaration or blueprint id found no declaration.

Mismatches found: none. I left the correct module and node record unchanged and
added this independent second reading. There are no hollow definitions, local
notations, private copies, or proved theorems: the only new declaration is the
named theorem with whole proof `by sorry`. All variables and universes are
explicitly bound; the node's `lean.statement` matches the source signature
verbatim. Compilation and delivery preflight results are recorded below.

Second-reader validation: the prescribed `scompile.py NL
lem-exc-weakly-etale-excellent` with the absolute sandbox file path exited 0
for both sandbox and library placements, with no diagnostics or warnings.
A direct string check confirmed the recorded signature and the 100-column limit.
The prescribed `deliver2.py NL lem-exc-weakly-etale-excellent --no-push`
printed `OK (dry run)` and exited 0: preflight and compilation both passed.
