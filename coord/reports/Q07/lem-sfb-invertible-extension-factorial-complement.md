## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleExtensionFactorialComplement` states
`AlgebraicGeometry.Scheme.Modules.exists_invertible_extension_of_factorial_complement`,
with `sorry` as its entire proof. It introduces no definitions. The statement was read
against Stacks Project, `literature/stacks-project/divisors.tex`, Tag 0BD9,
`lemma-extend-invertible-module` (the lemma and its proof beginning at line 7127).
The declaration docstring includes every step of the accepted stage-1 split, including
the coherent comparison maps at successor and limit stages. No statement correction,
new node, or dependency repair was needed.

Clause-by-clause correspondence:

- A scheme Z: `{Z : Scheme.{u}}`, with the explicit universe `universe u`.
- Z locally Noetherian: `[IsLocallyNoetherian Z]`, the recorded Mathlib class.
- An open subscheme U of Z: `(U : Z.Opens)`; its scheme is `U.toScheme` and its
  canonical open immersion is `U.ι`. An arbitrary open subscheme is isomorphic to
  this canonical open subscheme, exactly as def-weil-open-immersion states.
- Every point outside U has a UFD local ring:
  `hfactorial : ∀ z : Z, z ∉ U → IsDomain (Z.presheaf.stalk z) ∧
  UniqueFactorizationMonoid (Z.presheaf.stalk z)`.
  The stalk is the structure-sheaf local ring. Both conjuncts are necessary:
  `UniqueFactorizationMonoid` describes factorization and `IsDomain` specifies a
  domain. Mathlib's class docstring explicitly identifies their conjunction with
  a UFD and explains the equivalent finite prime factorization formulation.
- An arbitrary invertible O_U-module M: `(M : U.toScheme.Modules) [M.IsInvertible]`.
  This uses `Scheme.Modules.IsInvertible`, the dependency's locally free rank-one
  predicate, which also implies quasi-coherence.
- Existence of an O_Z-module extension: `∃ Mext : Z.Modules`.
- The extension is invertible: `Mext.IsInvertible`.
- Its restriction is isomorphic to M:
  `Nonempty ((tensorPullback U.ι).obj Mext ≅ M)`. The pullback is the actual
  inverse-image-and-tensor construction; along an open immersion it is module
  restriction. `Nonempty` expresses existence of an isomorphism, precisely the
  node's conclusion, rather than selecting an additional canonical extension.
- The final sentence of the node excludes extra assumptions or uniqueness claims:
  there are no density, integrality, separatedness, nonemptiness, or uniqueness
  binders or conclusions. Local Noetherianity is not replaced by global Noetherianity.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`, declaration
  `AlgebraicGeometry.IsLocallyNoetherian`. Its affine-cover equivalence and its
  open-immersion permanence results were also read in the source.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, declaration
  `AlgebraicGeometry.IsOpenImmersion`, together with the standard open-subscheme
  construction `Scheme.Opens.toScheme` and `U.ι` from the imported restriction API.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, declaration
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`. Its full local-trivialization
  signature and docstring were read, rather than substituting the different
  `SheafOfModules.IsInvertible` predicate.
- Added the already landed `def-pc-module-pullback` to `stmt_deps` to name the
  restriction construction explicitly. Its recorded module
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly imports
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, which defines
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from inverse image and change
  of rings. Both the recorded module and this full definition were read. No copy
  of the functor or additional assumption is introduced.

The proof imports are the stated proof dependencies:
`WeilConjectures.AlgebraicGeometry.EffectiveCartier` for the divisor line module,
`Sheaf.AlgebraicGeometry.CartierExtensionFactorialComplement` for
`Scheme.IdealSheafData.exists_isInvertible_extension_of_factorial_complement`, and
`Sheaf.CategoryTheory.SiteModuleSheafGluing` for
`SheafOfModules.exists_moduleSheaf_of_cover`. The quasi-compactness input
`lem-sfb-noetherian-open-immersion-qc` is the Mathlib instance in the already
imported `Mathlib.AlgebraicGeometry.Noetherian`. The proof-only dependency
`lem-sfb-quasiaffine-line-effective-divisor` currently has no recorded Lean
declaration or Mathlib match, so there is no module to import for it; it is retained
in the unchanged proof plan and docstring. It is not needed to type this statement.

Edge cases checked before writing:

- `U = ⊤`: the complement condition is vacuous, and M itself is an extension,
  up to the canonical isomorphism from the top open to Z. No UFD condition is imposed
  on any stalk in this case, so even nonreduced Z is permitted.
- `U = ⊥`: the input is the module on the empty scheme, and the structure module
  on Z provides the expected extension. The stated factorial condition then holds
  at every point; there is no artificial nonempty-open assumption.
- Empty Z: the stalk condition is vacuous and both module categories are those
  on the empty scheme. No `Nonempty Z` or domain of global sections is required.
- Disconnected Z, empty intersections in an affine cover, and components disjoint
  from U: none is excluded. No density or global-domain condition appears.
- Non-quasi-compact locally Noetherian Z and nonseparated Z remain admitted;
  there is no `CompactSpace`, `IsNoetherian`, or `IsSeparated` assumption.
- A singular point with a nonfactorial local ring outside U fails the actual
  hypothesis, as it must. Fields are allowed factorial local rings. Factoriality
  is required only outside U, with no restriction at singularities inside U.

Searches (2026-10-24), before writing the declaration:

- `msearch.py ... leanfinder`, query: "Every invertible module on an open
  subscheme of a locally Noetherian scheme extends if local rings outside the
  open are unique factorization domains". Eight returned hits concern tilde
  section representations, Noetherian stalks, affine basic-open denominators,
  and integrality of sections. None states extension of invertible modules.
- `msearch.py ... leansearch`, query: "Every line bundle on an open subset
  extends to a locally Noetherian scheme with factorial local rings on the
  complement". Eight returned hits concern Noetherian affine charts, scheme
  restriction, zero loci, and reduced open subschemes; none is the theorem.
- `msearch.py ... loogle`, query: `"IsInvertible", "tensorPullback"`.
  Zero hits.
- `msearch.py ... grep`, query:
  `(invertible|lineBundle|picard).*(extend|extension)|(extend|extension).*(invertible|lineBundle|picard)`
  under `Mathlib/AlgebraicGeometry`: zero hits.
- `rg -n` on `lean/WeilConjectures` and `lean/Sheaf`, query:
  `(invertible|Invertible|lineBundle).*(extend|extension)|(extend|extension).*(invertible|Invertible|lineBundle)`.
  Inspected the relevant results: `SmoothDVRGenericLineExtension.lean` states
  only the smooth finite-type DVR generic-fibre special case; the Cartier
  extension module extends effective Cartier divisors, not arbitrary invertible
  modules. The other extension hits concern unrelated tensor comparisons,
  Kummer monoids, or proof-docstring citations.
- `grep -rn "lem-sfb-invertible-extension-factorial-complement" lean/WeilConjectures`:
  zero hits. Exact declaration-name search in `lean/WeilConjectures`, `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: zero hits before creation.

Validation: `scompile.py Q07 lem-sfb-invertible-extension-factorial-complement`
compiled the delivered file cleanly as both `Sheaf.Stage2.Sandbox0` and
`Sheaf.AlgebraicGeometry.InvertibleExtensionFactorialComplement` (10.1 and 5.1
seconds). No diagnostics were emitted. All variables and universes are explicitly
bound; both implicit-auto-binding options are disabled.

## Second reading by Q07

The dispatcher requires a single worker and forbids starting another agent. This
section records the author's separate second pass with the node, Lean file, and
Tag 0BD9 open; the maintainer's independent reading is still required and is not
claimed here.

Rechecked that `{Z : Scheme.{u}}` and `[IsLocallyNoetherian Z]` impose precisely the
ambient assumptions; `U : Z.Opens` introduces every open of Z; the universal
quantifier ranges over points of Z and guards factoriality by `z ∉ U`; the
conjunction is a UFD of the structure-sheaf stalk, rather than of an affine chart
or global section ring. Rechecked that the input module is on `U.toScheme` and
uses the scheme-module invertibility predicate. The output module is on Z, its
invertibility is asserted, and the displayed isomorphism has exactly the required
direction from its canonical restriction to M. Rechecked empty and top opens,
empty and disconnected schemes, and the absence of quasi-compactness and density.
The added landed dependency supplies the canonical restriction functor without
changing the source statement. The proof imports match the available recorded
proof dependencies, and the docstring retains the transfinite coherence invariant
needed in the non-quasi-compact case. No mismatch or change was found on this pass.
