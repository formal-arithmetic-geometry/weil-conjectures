import pathlib,json,shutil,sys,subprocess
root=pathlib.Path(sys.argv[1]); p=root/'dag/nodes/sec-six-functors/lem-coef-infinity-functor-pushout.json';d=json.loads(p.read_text());s=d['proof'][6]['text'];n=s.count('\n'+'atural');print(root,'repaired natural macros',n)
assert n>0
shutil.copy2(p,str(p)+'.maint-N6-1792191600-tex.bak')
d['proof'][6]['text']=s.replace('\n'+'atural',r'\natural')
p.write_text(json.dumps(d,indent=1,ensure_ascii=False)+'\n')
subprocess.run(['git','-c','user.name=Bin Wu','-c','user.email=844524296@qq.com','commit','--only','-m','N6: preserve natural-marking formulas','--',str(p.relative_to(root))],cwd=root,check=True)
