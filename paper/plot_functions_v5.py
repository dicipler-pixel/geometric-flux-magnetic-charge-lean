from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root=Path(__file__).resolve().parent
(root/'figures').mkdir(exist_ok=True)
plt.rcParams.update({'pdf.fonttype':42,'ps.fonttype':42,'font.family':'DejaVu Serif','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
x=np.linspace(0,np.pi,601);n=(1-np.cos(x))/2;s=-(1+np.cos(x))/2;w=np.sin(x)/2
fig,ax=plt.subplots(1,2,figsize=(8.7,3.1),constrained_layout=True)
ax[0].plot(x,w,color='#135b78',lw=2,label=r'$C_-=\sin\theta/2$')
ax[0].plot(x,-w,color='#b46b20',lw=2,label=r'$C_+=-\sin\theta/2$')
ax[0].fill_between(x,0,w,color='#135b78',alpha=.12)
ax[0].fill_between(x,0,-w,color='#b46b20',alpha=.12)
ax[0].axhline(0,color='#555555',lw=.6)
ax[0].set_ylim(-.62,.62);ax[0].set_title('(a) Derived band curvatures',loc='left',fontsize=10)
ax[0].legend(frameon=False,fontsize=9,loc='lower center',bbox_to_anchor=(.5,-.44),ncol=2)
ax[1].plot(x,n,color='#135b78',lw=2,label=r'$a_N$')
ax[1].plot(x,s,color='#b46b20',lw=2,label=r'$a_S$')
ax[1].plot(x,n-s,color='#444444',ls='--',lw=1.3,label=r'$a_N-a_S=1$')
ax[1].set_title('(b) Fixed chart coefficients',loc='left',fontsize=10)
ax[1].set_ylim(-1.12,1.18)
ax[1].legend(frameon=False,ncol=3,loc='lower center',bbox_to_anchor=(.5,-.44),fontsize=9)
for a in ax:
 a.set_xticks([0,np.pi/2,np.pi],['0',r'$\pi/2$',r'$\pi$']);a.set_xlim(0,np.pi);a.set_xlabel(r'$\theta$');a.grid(alpha=.15)
fig.savefig(root/'figures/curvature_and_gauges_v5.pdf',bbox_inches='tight')
fig.savefig(root/'figures/curvature_and_gauges_v5.png',dpi=200,bbox_inches='tight')
