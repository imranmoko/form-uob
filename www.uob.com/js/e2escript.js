var encString='';
var isFirstReq = true;
var e2eSub = false;
var e2eApplet = new E2EApplet();
function checkReset(){
	return false;
}

function doPagination(e2eFlag,actionUrl) {
    	e2esubmit(e2eFlag,actionUrl);
	}

    function disableLnk() {
            for (var i=1; i<4; i++) {
                link = document.getElementById("nxtPage"+i);
	            if(link != null){
	            	link.oldOnClick = link.onclick;
	            	link.onclick = cancelLink;
	            	link.style.cursor = 'default';
	            	link.disabled = true;
	            }
            }
            
            for (var i=1; i<4; i++) {
	            link = document.getElementById("prvPage"+i);
	            if(link != null){
	            	link.oldOnClick = link.onclick;
	            	link.onclick = cancelLink;
	            	link.style.cursor = 'default';
	            	link.disabled = true;
	            }
            }
      }
      
      function cancelLink () {
            return false;
      }
function e2eValidateSubmit (validateFlag,e2eFlag,actionUrl){
	if(validateFlag)	
	{
		e2esubmit(e2eFlag,actionUrl);
	} else {
		return false;
	}
} 
		
function e2esubmit(e2eFlag,actionUrl){
	
	if(document.getElementById('favoritesList')){
		document.getElementById('favoritesList').disabled=true;
	}
	if(checkSubmitAction()){
		if(e2eFlag)	{
			e2eApplet = new E2EApplet();
			var challenge=document.getElementById('challenge').value;
			var pubKey=document.getElementById('publicKey').value;
			if(encryptForm(challenge,pubKey)){
				document.forms[1].action=actionUrl;
				hdivVal=$('input[name="__c"]').val();
				$("#dummyFormId").append('<input type="hidden" name="__c" value="'+hdivVal+'">');
				/*hdivVal=$('input[name="_HDIV_STATE_"]').val();
				$("#dummyFormId").append('<input type="hidden" name="_HDIV_STATE_" value="'+hdivVal+'">');*/
				try{
					loader();
					fader();
				 }catch(err){}
				document.forms[1].submit();
			}else{
				return false;
			}

		
		}else {
			isFirstReq = false;
			document.forms[0].action=actionUrl;
			try{
				loader();
				fader();
			 }catch(err){}
			document.forms[0].submit();
		}
	}
	else {
		return false;
    }
	    isFirstReq = true;
	    return false;
    }
//}

function setSubmitVal(){
	if(document.getElementById('favoritesList')){
		document.getElementById('favoritesList').disabled=true;
	}
	if(!checkSubmitAction()){
		return false;
	}
    else {
		isFirstReq = false;
    }
}



function checkSubmitAction(){
	if(isFirstReq){
		return true;
	}
	else {
		return false;
	}
}


function encryptForm(challenge,pubKey)
{
try{
	
	isFirstReq = false;
	var inputFields=document.forms[0].elements;
	
    for (var i=0;i<inputFields.length;i++) 
    {    
        if (inputFields[i].name)
        {
			
			var key=inputFields[i].name;
			var value=inputFields[i].value;
			
			value = convertChar2CP(value);
			if((inputFields[i].type == 'checkbox' || inputFields[i].type == 'radio'))
			{
				if(inputFields[i].checked)
				{
				
					
					e2eApplet.addParameter(key,value);
				}
			} else {
				e2eApplet.addParameter(key,value);
			}
		}
	}
	
	
	generateDesKeyandParamString(challenge,pubKey);   
	return true;  
	
	}catch(err){	
	    isFirstReq = true;
		return false;
    }

 }
 
 
 function generateDesKeyandParamString(challenge,pubKey)
{

 	var inputElm=document.forms[1].elements;

	for(var k=0;k<inputElm.length;k++)
	{
		if(inputElm[k].id=='encData')
		{
			inputElm[k].value = e2eApplet.doFinal(pubKey, challenge);
		}
	}
	
 }
 
 function popup(url){
 var st1 = Math.round((Math.random() * 999999999)); 
 var cc_url =window.location.protocol + '//' + window.location.host;
 window.open(cc_url + url,"CardActivation"+st1,"toolbar=no,location=no,directories=no,status=no,menubar=no,scrollbars=yes,resizable=no,height= 600,width= 900,left = 120,top = 100");

}
 
function popupExternalSite(url, title) {
	var st1 = Math.round((Math.random() * 999999999)); 
	window.open(url,title+st1,"toolbar=no,location=no,directories=no,status=no,menubar=no,scrollbars=yes,resizable=no,height= 600,width= 900,left = 120,top = 100");
}
 function convertChar2CP(textString) { 
	var haut = 0;
	var n = 0;
	var CPstring = '';
	for (var i = 0; i < textString.length; i++) {
		var b = textString.charCodeAt(i); 
		if (b < 0 || b > 0xFFFF) {
			CPstring += 'Error in convertChar2CP: byte out of range ' + dec2hex(b) + '!';
			}
		if (haut != 0) {
			if (0xDC00 <= b && b <= 0xDFFF) {
				CPstring += dec2hex(0x10000 + ((haut - 0xD800) << 10) + (b - 0xDC00)) + ' ';
				haut = 0;
				continue;
				}
			else {
				CPstring += 'Error in convertChar2CP: surrogate out of range ' + dec2hex(haut) + '!';
				haut = 0;
				}
			}
		if (0xD800 <= b && b <= 0xDBFF) {
			haut = b;
			}
		else {
			CPstring += dec2hex(b) + ' ';
			}
		}
	return CPstring.substring(0, CPstring.length-1);
	}
function dec2hex ( textString ) {
	return (textString+0).toString(16).toUpperCase();
	}
 

function e2eFrmValidateSubmit (validateFlag,e2eFlag,actionUrl,fName){
	if(validateFlag)	
	{
		e2eFrmsubmit(e2eFlag,actionUrl,fName);
	} else {
		return false;
	}
} 
		
function e2eFrmsubmit(e2eFlag,actionUrl,fName){
	try{
		loader();
		fader();
		if(document.getElementById('favoritesList')){
			document.getElementById('favoritesList').disabled=true;
		}
		if(checkSubmitAction()){
			if(e2eFlag)	{
				e2eApplet = new E2EApplet();
				var challenge=document.getElementById('challenge').value;
				var pubKey=document.getElementById('publicKey').value;
				if(encryptFrmForm(challenge,pubKey,fName)){
					//document.forms[1].action=actionUrl;
					//$("#dummyFormId").action=actionUrl;
					$("#dummyFormId").attr("action", actionUrl);
					hdivVal=$('form[name='+fName+'] input[name="__c"]').val();
					$("#dummyFormId").append('<input type="hidden" name="__c" value="'+hdivVal+'">');
					/*hdivVal=$('input[name="_HDIV_STATE_"]').val();
					$("#dummyFormId").append('<input type="hidden" name="_HDIV_STATE_" value="'+hdivVal+'">');*/
					//document.forms[1].submit();
					$("#dummyFormId").submit();
				}else{
					return false;
				}
	
			
			}else {
				isFirstReq = false;
				/*document.forms[0].action=actionUrl;
				document.forms[0].submit();*/
				//var formName = "form[name="+fname+"]";
				//alert("formName :; =="+formName)
				$("form[name="+fName+"]").attr("action", actionUrl);
				$("form[name="+fName+"]").submit();
			}
		}
		else {
			return false;
	    }
    }catch(err){
	    isFirstReq = true;
	    return false;
    }
}


function encryptFrmForm(challenge,pubKey,fName)
{
try{
	
	isFirstReq = false;
	//var inputFields=document.forms[0].elements;
	
	var inputFields=$("form[name="+fName+"] input");
	
    for (var i=0;i<inputFields.length;i++) 
    {    
        if (inputFields[i].name)
        {
			
			var key=inputFields[i].name;
			var value=inputFields[i].value;
			
			value = convertChar2CP(value);
			if((inputFields[i].type == 'checkbox' || inputFields[i].type == 'radio'))
			{
				if(inputFields[i].checked)
				{
				
					
					e2eApplet.addParameter(key,value);
				}
			} else {
				e2eApplet.addParameter(key,value);
			}
		}
	}
	
	
	generateDesKeyandParamString(challenge,pubKey);   
	return true;  
	
	}catch(err){	
	    isFirstReq = true;
		return false;
    }

 }
