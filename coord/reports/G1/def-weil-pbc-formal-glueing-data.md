## Worker report

The module defines `FormalGlueing.Data`, its compatible morphisms
`FormalGlueing.Hom`, componentwise identity and composition, and the resulting
`CategoryTheory.Category` instance. It states auxiliary existence and
well-definedness facts with named `sorry` proofs. The canonical-map facts belong
to the already recorded pointer
`lem-weil-pbc-formal-glueing-canonical-maps`; the category compatibility facts
belong to this definition node. No definition contains `sorry` as data.

The binders `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`,
`(φ : R →+* S)`, `{t : ℕ}`, and `(f : Fin t → R)` render the commutative
rings, homomorphism and the finite list of elements. The module structures are
`ModuleCat` objects;
`restrict` uses `Module.compHom` along `φ`, and `piece` restricts along the
canonical map to `Localization.Away (f i)`.

For the objects, `Data.M'` is the S-module; `Data.M i` is the
`Localization.Away (f i)`-module. `Data.alpha i` is an R-linear isomorphism
from `localize (f i) (restrict φ M')` to the R-restriction of
`extend φ (piece (f i) (M i))`; `Data.alpha_smul` makes it S-linear for the
canonical localized action. `Data.alpha_overlap i j` is the specified R-linear
isomorphism `(M_i)_(f_j) ≃ (M_j)_(f_i)`. `Data.square` renders clause (a),
with the left path `localMap alpha_i`, `compare`, `extendMapR alpha_ij` and
the right path `swap`, `localMap alpha_j`, `compare`. `Data.cocycle` renders
clause (b), with exactly the three maps on each side in the node and source
`((M_i)_(f_j))_(f_k)` and target `((M_k)_(f_j))_(f_i)`.

For morphisms, `Hom.prime` is the S-linear `u'`, and `Hom.chart i` is the
R-linear `u_i`. `Hom.prime_compat` is the first displayed morphism equation;
`Hom.chart_compat` is the second. `idHom` and `compHom` provide the specified
componentwise identities and composition; the category instance uses their
laws. The `R_f`-linearity implicit in the source follows from R-linearity and
invertibility of f on both chart modules.

`localize` is `LocalizedModule.Away`; `localMap` uses
`IsLocalizedModule.map`. `extend` is Mathlib's `S ⊗[R] M`, canonically the
node's `M ⊗[R] S`, and `extendMap` uses `LinearMap.baseChange`. `swap` and
`compare` are selected from unique maps specified on the original module and
on pure tensors respectively. `compare_smul` records S-linearity, and
`localizedSModule` uses the action determined on fractions by
`exists_localized_s_module`.

Dependency declarations read: `LocalizedModule.Away` and
`IsLocalizedModule.map`, `Mathlib.Algebra.Module.LocalizedModule.Basic`;
`Localization.Away`, `Mathlib.GroupTheory.MonoidLocalization.Away`;
`LinearMap.baseChange`, `Mathlib.LinearAlgebra.TensorProduct.Tower`;
`CategoryTheory.Category`, `Mathlib.CategoryTheory.Category.Basic`.
These correspond respectively to the five `stmt_deps`, including
`def-weil-pbc-module-localization` through `IsLocalizedModule.map`.

Edge cases: an empty index type leaves the compatibility fields vacuous and
still has the S-module component; a singleton retains both square and
cocycle equations; `f i = 0`, the zero module, and characteristic zero or
positive characteristic are not excluded. There is no flatness or finiteness
hypothesis on `φ` or the modules. Universe binders are explicit.

Searches performed: `msearch.py` LeanFinder, query "category of formal
glueing data for modules over a ring homomorphism and principal localizations
with cocycle compatibility": eight hits, including
`ModuleCat.localizedModule_functor` and `CategoryTheory.GlueData`, none this
module category. `msearch.py` Loogle, query
`GlueData,ModuleCat,LocalizedModule`: zero hits. `msearch.py` grep for
`GlueData|FormalGlue|GlueingData` in Mathlib/Algebra: zero hits; grep in
Mathlib/CategoryTheory finds only gluing data of spaces. `rg` of the source
repository and the project's Lean finds gluing of schemes and spaces, but no
formal glueing category for modules. `rg` of `dag/lean_names_upstream.json`
finds no declaration for this item, and the required grep of the item ID in
`WeilConjectures` has no hit. The DAG node already records earlier broader
LeanFinder, LeanSearch, Loogle and Mathlib grep searches with the same result.

## Earlier second reading (a previous round; superseded)

I reread the node statement and complete module. The `Data` fields render the
S-module, localized R_f-modules, both families of isomorphisms, and equations
(a) and (b), with the same index types and sources and targets. `Hom` renders
the two compatibility equations for an S-linear map and R-linear chart maps.
`idHom`, `compHom`, and the category instance render componentwise identity,
composition, and category laws. The empty index case remains valid because
indexed fields are vacuous; no flatness, finiteness, or characteristic
assumptions were added. No mismatch was found and no correction was needed.

## Second reading by G1

Independent review of the sandbox node and all 315 lines of its module against
Stacks More on Algebra, Remark 05EL, `remark-glueing-data`, items (1) and (2).
The repository lacks its literature checkout; I read the same source at
`/home/ubuntu/c1-stacks-review/more-algebra.tex:24641`, including Section 05E5
at line 24207. The section's opening Noetherian scheme is motivation for
coherent sheaves; the remark restarts with an arbitrary ring map and elements.
It imposes no Noetherian, flatness, completeness, or finite-module hypothesis.
The ideal generated by the elements is notation and supplies no extra data.

Objects, hypotheses, and clauses, matched independently:

- Commutative rings R and S: `{R : Type u} {S : Type v}` and `[CommRing R]
  `[CommRing S]`. Verdict: exact; zero rings and arbitrary characteristics
  are allowed. The ring map is `φ : R →+* S`, with no extra hypotheses.
- Finite list of elements: `{t : ℕ}` and `f : Fin t → R`. Verdict: exact;
  indexing from zero instead of one only renames the finite list.
- Module localization and localized maps: `localize` is an abbreviation
  using `LocalizedModule.Away`; `localMap` uses `IsLocalizedModule.map`
  and `LocalizedModule.mkLinearMap`. Verdict: these are the dependency
  notions, not replacement localization constructions.
- Restriction and scalar extension: `restrict` installs `Module.compHom`
  along the explicit map; `extend` uses `φ.toAlgebra` and `S ⊗[R] M`;
  `extendMap` is `LinearMap.baseChange S`. Verdict: exact through tensor
  commutation, which is already the base-change dependency's convention.
- Canonical S-action on localized S-modules: `exists_localized_s_module`
  specifies its value on every fraction; `localizedSModule` chooses that
  module structure. Verdict: the formula uniquely determines the action,
  and no arbitrary action enters the object data. `localMap_smul` is the
  recorded canonical-maps pointer's linearity clause.
- Canonical interchange and comparison maps: `exists_swap` specifies unique
  R-linear extension of the original module's double localization map;
  `exists_compare` specifies unique R-linear extension of the tensor of
  `mkLinearMap`. `swap` and `compare` choose those maps. Verdict: exact
  universal-property descriptions of sigma and c, with the node's source,
  target, and fraction formulas; `compare_smul` gives S-linearity.
- S-module M': `Data.M' : ModuleCat.{w} S`. Verdict: exact.
- R localized at f_i modules M_i: `Data.M i : ModuleCat.{w}
  (Localization.Away (f i))`; `piece` restricts them along the canonical
  algebra map. Verdict: exact, without an invertibility hypothesis supplied
  externally by the user.
- S-linear isomorphisms alpha_i: `Data.alpha i` is the R-linear equivalence
  between the required underlying modules; `Data.alpha_smul` requires
  commutation with every S-scalar. Verdict: together these are precisely
  an S-linear bijection, with S-linear inverse following from bijectivity.
- R-linear overlap isomorphisms alpha_ij: `Data.alpha_overlap i j` is
  `localize (f j) (piece (f i) (M i)) ≃ₗ[R]
  localize (f i) (piece (f j) (M j))`. Verdict: exact.
- Condition (a), every i,j: `Data.square` has left path
  `localMap alpha_i`, then `compare`, then `extendMapR alpha_overlap`;
  right path `swap`, then `localMap alpha_j`, then `compare`. Verdict:
  exact equality from `(M'_fi)_fj` to `(M_j)_fi ⊗ S`, in the stated order.
- Condition (b), every i,j,k: `Data.cocycle` has left path
  `localMap alpha_ij` at f_k, `swap` at f_i,f_k on M_j,
  `localMap alpha_jk` at f_i; right path `swap` at f_j,f_k on M_i,
  `localMap alpha_ik` at f_j, `swap` at f_i,f_j on M_k. Verdict: exact
  equality from `((M_i)_fj)_fk` to `((M_k)_fj)_fi`.
- Morphisms: `Hom.prime` is S-linear and `Hom.chart i` is R-linear on
  the restricted chart modules. Verdict: exact; the implicit localized
  scalar linearity follows from invertibility of denominators.
- First morphism equation: `Hom.prime_compat` is
  beta_i composed with localized u' = base-changed u_i composed with alpha_i.
  Second equation: `Hom.chart_compat` is beta_ij composed with localized
  u_i = localized u_j composed with alpha_ij. Verdict: exact for all i,j.
- Componentwise identities and composition: `idHom` uses identity prime
  and chart maps; `compHom` uses `v.prime.comp u.prime` and
  `(v.chart i).comp (u.chart i)`. Their proof fields use named theorems
  `id_compat` and `comp_compat`; `category_laws` provides the laws for the
  `CategoryTheory.Category` instance. Verdict: exact category structure;
  Mathlib's diagrammatic composition order is respected.

I opened every dependency node and its recorded Mathlib signature:
`LocalizedModule.Away` (Basic.lean:1475), `LocalizedModule` (:89),
`mkLinearMap` (:492), `IsLocalizedModule.map` (:1227), `Localization.Away`
(MonoidLocalization/Away.lean:142), `LinearMap.baseChange` (Tower.lean:661,
including its identity and composition formulas), and `CategoryTheory.Category`
(Category/Basic.lean:234). Their hypotheses admit exactly the specializations
used here. No dependency module or new node is included, and none is needed.
The node has no statement correction; there are no correction verdicts to audit.
The canonical-map auxiliary theorems match clauses (1)-(3) of the node's
existing pointer to `lem-weil-pbc-formal-glueing-canonical-maps`; the category
compatibility facts match this definition node's recorded one-line checks.

Edge cases: t = 0 leaves just M' and its S-linear morphisms, since every
indexed structure field is vacuous. Repeated indices remain quantified,
including the singleton case. Zero modules, zero rings, f_i = 0 (localization
is zero), nilpotent or invertible elements, and all characteristics are
allowed. There is no scheme or integer n in this definition. Explicit ring
universes u,v and arbitrary module universe w do not require u = v or a
Small instance; any finite family of modules can be placed in a common large
enough universe. Localization and tensor universes use max as needed.

Independent searches used different words from the worker: LeanFinder via
msearch, query "patching modules with a module over S and modules over
principal localizations compatible on double overlaps", returned eight
localization/module scalar extension hits, none a patching-data category.
Loogle via msearch, query `"FormalGlueing"`, returned zero hits. LeanSearch,
query "category of patching data consisting of modules over S and R localized
at finitely many elements with overlap isomorphisms", was unavailable with
an internal server error; I recorded no verdict from that service. Ripgrep
for `patching|beauville|laszlo|formal.{0,5}glu` across Mathlib Algebra and
RingTheory, the upstream WeilConjectures tree, and the project's Sheaf tree
returned no matching definition. Searching `patching|glueing data|gluing data`
in Mathlib CategoryTheory and both project trees returned only generic
GlueData and scheme glueing uses. I opened `CategoryTheory.GlueData` and
`Pseudofunctor.DescentData`: the former has monomorphisms and pullbacks in one
category, and the latter requires overlap maps also over S tensor S; neither
is this formal module glueing category. A name search of
`dag/lean_names_upstream.json` and Sheaf found no FormalGlueing declaration.
Thus retaining the new module is correct.

Mismatch found: auxiliary theorem docstrings identified their constructions
but did not give complete step-by-step proof plans. I expanded the five
canonical-map theorem docstrings with the fraction formulas, universal
properties, uniqueness and linearity arguments, and the three category
compatibility/law theorem docstrings with the componentwise arguments. I also
added the delivery node's blueprint tag to the canonical-map theorems while
retaining their pointer-node tags. All signatures, definitions and equations
were left unchanged. There is no hollow data definition, axiom, or completed
theorem proof: each postponed proof is a named theorem with `sorry`.
The recorded `lean.statement` equals the Data signature verbatim.
