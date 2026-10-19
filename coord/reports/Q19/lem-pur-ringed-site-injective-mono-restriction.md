## Worker report

The module `lean/Sheaf/CategoryTheory/RingedSiteInjectiveMonoRestriction.lean`
states `CategoryTheory.injective_ringed_site_mono_restriction`.  It gives the
Tag 093X assertion for sheaves of modules over a sheaf of commutative unital
rings on a small Grothendieck site.  No definition data is introduced and the
theorem proof is `sorry`, as required at stage 2.

The Lean rendering of each part of the node statement is:

* `{C : Type u} [SmallCategory C]` supplies a small category of site objects
  and arrows.
* `(J : Precoverage C) (_hJ : J.IsSiteForCoverings)` supplies exactly the
  covering axioms of the recorded site dependency, and `J.toGrothendieck` is
  its associated topology. No covering or subcanonicality hypothesis is
  imposed on the morphism `m`.
* `(O : Sheaf J.toGrothendieck CommRingCat.{u})` is the sheaf of commutative rings with one. Its standard
  forgetful functor to `RingCat` supplies precisely the coefficients required
  by the module category.
* `(I : ringedSiteModules.{u}
  ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj O))` is the sheaf of `O`-modules, using the
  dependency's abbreviation for Mathlib's `SheafOfModules`.
* `[Injective I]` is `CategoryTheory.Injective` in that module-sheaf category.
* `{W T : C} (m : W ⟶ T) [Mono m]` introduces an arbitrary monomorphism in the
  site.
* `Function.Surjective (I.val.map m.op).hom` is surjectivity of the module
  homomorphism from the sections over `T` to the sections over `W`; the
  contravariant map uses `m.op`.

The dependencies used are `CategoryTheory.Precoverage.IsSiteForCoverings` from
`Sheaf.CategoryTheory.SiteCoveringAxioms`, the universe convention
`def-weil-size-convention` (realized by the explicit common universe `u`),
`CategoryTheory.ringedSiteModules` from `Sheaf.CategoryTheory.RingedSiteModules`,
and `CategoryTheory.Injective` from
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`.  The size convention has
no Lean declaration of its own.  The module imports the first, third and
fourth interfaces; no private copy of any notion is made.

I checked the edge cases before fixing the signature: `m = 𝟙 T` gives the
identity restriction; the zero ring and zero module give a surjective zero map;
an empty site or empty object introduces no extra condition; and no
subcanonicality or covering condition on `m` is needed.  The signature does
not assume injectivity after forgetting the `O`-module structure.

Searches made:

* `msearch.py Q19 lem-pur-ringed-site-injective-mono-restriction leanfinder
  "injective sheaf of modules restriction along a monomorphism of a ringed site
  is surjective"`: returned eight hits, all concerning componentwise
  presheaf-morphism injectivity, locally injective sheafification, or generic
  sheaf factorization; no exact theorem.
* `msearch.py ... loogle "SheafOfModules Injective restriction surjective"`:
  returned zero hits because `Injective` was unknown to that query service.
  Retried with `"SheafOfModules", "Injective"`: six hits, all componentwise
  injectivity, local injectivity, or derivations; none states this result.
* `msearch.py ... grep "injective.*mono.*restriction|restriction.*surject"
  CategoryTheory`: returned zero hits.
* `rg -n
  'injective.*ringed.*site|ringed.*injective.*restriction|injective_ringed_site_mono_restriction'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures
  /home/ubuntu/weil-newtargets-shared/lean/Sheaf`: found no exact existing
  declaration.  The project's `InjectiveRestrictionSurjective` theorem is for
  opens of a ringed space and has a different statement.

The inherited stage-1 searches recorded in the node were also read; their
Mathlib hits distinguish `PresheafOfModules.injective_of_mono` (injectivity of
components of a morphism) from injectivity of an object, so they do not
duplicate this theorem.  No `STATEMENT-DISPUTED` flag or node fault was found.

Validation: the required `scompile.py` invocation compiled the sandbox wrapper
and the library module successfully, with no errors or warnings other than the
expected `sorry` declaration warning.


## Final signature audit

The initial draft used `RingCat`, whose objects need not be commutative. I
replaced the coefficient with `O : Sheaf J.toGrothendieck CommRingCat.{u}` and used the
standard `sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)` solely to pass its
underlying ring sheaf to the recorded module category. Ring limits provide
this sheaf-composition instance; no extra instance hypothesis is assumed.
The original node statement and dependencies are unchanged.

The declaration's docstring now follows all five DAG proof steps explicitly,
including the basis-map naturality, coordinate cancellation, exactness of
module sheafification and the identification of precomposition with the actual
restriction. Its proof dependencies are imported as ordinary imports from
Mathlib's `Presheaf.Generator` and `Presheaf.Sheafification`; the primary
statement interfaces are public imports. The module is placed under
`Sheaf.CategoryTheory`, its mathematical topic.

The earlier worker's stale-dispatch explanation conflated the accepted stage-1
split by Q09 (ledger line 31100) with a stage-2 statement. The current shared
node has no Lean record, so this delivery adds that record without resplitting
or changing its accepted proof. The prescribed first dry run reported the
missing branch field and the line-broken blueprint tag; both were repaired.
Independent mathematical review remains the maintainer's, as in this dispatch.

## Second reading by Q19

Independent maintainer reading of immutable delivery 3b3b5286848a32c67b54006c365ee6974020a593, performed on 2026-10-18.


I started with packet.md and read check-brief2.md in full, the stage-2 brief and delivery-errors H. I inspected the immutable item JSON, all four immutable statement-dependency records, the delivered module and report. Dependency implementations were read in the read-only Q19 clone and pinned Mathlib sources; delivery contents were taken from snapshot.

* Small site: `{C : Type u} [SmallCategory C]`, `J : Precoverage C` and `_hJ : J.IsSiteForCoverings` use the recorded `CategoryTheory.Precoverage.IsSiteForCoverings`. I opened SiteCoveringAxioms.lean: its actual fields give isomorphism coverings, bind composition and existence of covering pullbacks. It requires no global pullback instance. The associated topology is `J.toGrothendieck`. The otherwise unused `_hJ` faithfully records the site's covering axioms, rather than a hollow tautology.
* Common universe: the single explicit `universe u` contains objects, morphisms, covering indices, ring carriers and module carriers. `ringedSiteModules.{u}` fixes the module universe to this bound. This is precisely the item's stated common-universe convention, not a silent repair forcing independent universes equal. The size dependency is correctly recorded as a metatheoretic convention with no declaration.
* Coefficients: `O : Sheaf J.toGrothendieck CommRingCat.{u}` gives commutative unital rings. `sheafCompose ... (forget₂ CommRingCat RingCat)` keeps the same underlying sheaf and restrictions while supplying the coefficient interface for modules; it does not replace O by a constant ring. The Ring.Limits import supports this sheaf composition without an extra instance hypothesis.
* Module sheaf: I opened RingedSiteModules.lean. Its public abbreviation is exactly `SheafOfModules.{v} R`, with Mathlib's category, not a private reconstruction. Mathlib Sheaf.lean:33 and its Hom/category definitions agree with the dependency: underlying presheaves of modules, sheaf condition on abelian groups, and sectionwise linear natural morphisms. Presheaf.lean supplies semilinear restriction maps with the correct ring restriction. The abelian instance in Sheaf/Abelian.lean:40 uses sheafification and locally bijective equivalences, available in the common small universe; these are not added assumptions on the theorem.
* Injectivity: `[Injective I]` resolves in the module-sheaf category. I read Injective/Basic.lean:32: its `factors` field extends any morphism into I along every mono, exactly the dependency's Hom-surjectivity clause. It does not assert injectivity of the underlying abelian sheaf, and enough injectives is not needed for this statement about a given I.
* Quantifiers and conclusion: `{W T : C} (m : W ⟶ T) [Mono m]` allows every site monomorphism. `m.op` points from T to W in the opposite category. By PresheafOfModules.map, `(I.val.map m.op).hom` is precisely restriction I(T) to I(W), with scalar restriction on its target. `Function.Surjective` is exactly the entire conclusion. No covering, subcanonicality, scheme, topological-space or pro-etale substitute appears.

All binders and the universe are bound; `autoImplicit false` is set. A programmatic comparison confirmed the node's `lean.statement` equals the file signature verbatim, excluding only `:= by sorry`. The record has all required fields and the correct module, file, namespace and branch.

## Source and proof-plan checks

I read Q19/literature/stacks-project/sites-cohomology.tex:1962-2009, Tag 093X, including the complete proof. It assumes a ringed site, a site mono and an injective module sheaf, and concludes the stated restriction is surjective. conventions.tex:51 explicitly makes rings commutative with one and allows the zero ring.

I also read sites.tex:679ff (00VH and the clarification allowing some choice of covering fibre products); sites-modules.tex:782ff (module sheaves), 815ff and 865ff (module sheafification and its adjunction), 874ff (exactness, 03EI), 1337ff (abelian category, 03DA), and 2149ff (the evaluation identity following 03DI). The size-convention and injective-resolution blueprint source files were opened.

The delivered module and theorem docstrings have the precise source label and blueprint ID. The theorem docstring carries all five accepted DAG steps: free representability and sheafification; natural basis map; coordinatewise injectivity and categorical monicity; preservation of monos by exact sheafification; and injective extension identified with restriction via the identity generator. I checked the direction of the composites and that no natural coefficient-recovery retraction is asserted. Mathlib Presheaf/Generator.lean:58 gives `freeYonedaEquiv`, and Presheaf/Sheafification.lean supplies the adjunction and the finite-limit-preservation instance at its end. These proof interfaces are ordinarily imported; statement interfaces are public imports. No extra prerequisite or helper construction is missing from this statement.

## Reuse, edge cases and pilot gates

I audited the recorded LeanSearch, LeanFinder/Loogle and grep results, and independently searched project, upstream and ModuleCat sources using restriction-surjectivity and section-extension phrases. I opened the nearest declarations: InjectiveSheafMonoRestriction.lean concerns injective abelian sheaves; AlgebraicGeometry/InjectiveRestrictionSurjective.lean concerns opens of a ringed space. Neither states this arbitrary-ringed-site module theorem. Componentwise `PresheafOfModules.injective_of_mono` concerns a morphism, not an injective object. All notions in the delivered theorem use their dependency interfaces or Mathlib; no duplicate definition was introduced.

Edge cases checked: identity and arbitrary isomorphism m; empty category (no W or T); zero module; zero coefficient ring (all unitary modules trivial); empty covering of an object (sheaf sections there are trivial, and pullback of that covering treats the source); arbitrary characteristic; and non-subcanonical sites. On the one-object trivial site with coefficient ring Z/2, module-injectivity need not imply abelian-group-injectivity, and the theorem correctly requires only the former.

There is one declaration and its proof is only `by sorry`. There are no data definitions, local proofs, local instances, private notions, arbitrary replacement maps or hollow constructions. Every Lean line is at most 100 characters. No statement correction, new node or dependency repair was made, so no §1(C) citer audit is applicable.

## Compiler evidence

Reproduced from the immutable file with:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q19 lem-pur-ringed-site-injective-mono-restriction snapshot/lean/Sheaf/CategoryTheory/RingedSiteInjectiveMonoRestriction.lean
```

Exit code 0. Output reported sandbox `Sheaf/Stage2/Sandbox0.lean` compiled in 2.3 s and library `Sheaf/CategoryTheory/RingedSiteInjectiveMonoRestriction.lean` in 2.4 s, with no diagnostics. Each invocation had the prescribed 60-second limit. The installed wrapper identifies itself as the server-side overlay implementation and produced an isolated `/dev/shm/nt-tmp/nt-local-compile-.../.lbuild` result; I used the prescribed wrapper rather than invoking ssh or a compiler directly. The report's previous compile claim is therefore independently reproduced. No global build, live Lean write, Git mutation, claim, merge or delivery was performed.

The only mismatch was H11: this section was previously a placeholder. This complete second reading replaces it. No mathematical, Lean-signature or dependency-record correction was needed.
